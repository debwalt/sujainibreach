#!/usr/bin/env python3
"""
quiz_bot_memory_recalibrate.py

Behavior:
- Uses per-question CSV memory (auto-created) to track proven True / False options.
- If computed answer maps to a proven-False option for the same question:
    - Recompute answer variants (all printed outputs, integer/fraction variants, stripped text).
    - Try to match variants to options while avoiding proven-False.
    - If still conflicts, score all options (numeric distance or text similarity) and choose top non-false.
- Deterministic; no randomness. Durable CSV writes and caching for efficiency.
- Compatible with modes 'runtunan' and 'percabangan'.
"""

import asyncio
from playwright.async_api import async_playwright, TimeoutError as PlaywrightTimeoutError
import re, math, time, sys, traceback, csv, os, hashlib, difflib
from fractions import Fraction
from datetime import datetime

# ---------- CONFIG ----------
WORKERS = {"runtunan": 2, "percabangan": 2}
HEADLESS = True
RESTART_DELAY_S = 1.0
MAX_RESTARTS_PER_WORKER = None
QUESTION_TIMEOUT = 6000
NAV_TIMEOUT = 6000

MEMORY_CSV = "quiz_memory.csv"
# ---------------------------------

# ---------- Normalization helpers ----------
_whitespace_re = re.compile(r'\s+')
def normalize_text(qt):
    if not qt:
        return []
    qt = qt.replace('\xa0', ' ')
    qt = qt.replace('←', '<-')
    qt = qt.replace('–', '-')
    qt = qt.replace('\u2003', ' ')
    qt = re.sub(r'\b(DAN|AND)\b', 'and', qt, flags=re.IGNORECASE)
    qt = re.sub(r'\b(ATAU|OR)\b', 'or', qt, flags=re.IGNORECASE)
    qt = re.sub(r'\b(TIDAK|NOT)\b', 'not', qt, flags=re.IGNORECASE)
    qt = re.sub(r'\bmod\b', '%', qt, flags=re.IGNORECASE)
    qt = re.sub(r'\bdiv\b', '//', qt, flags=re.IGNORECASE)
    lines = [ln.strip() for ln in qt.splitlines() if ln.strip()]
    return lines

def normalize_choice_text(s):
    if s is None:
        return ""
    s = str(s)
    s = s.replace('\xa0', ' ')
    s = s.strip()
    s = _whitespace_re.sub(' ', s)
    s = s.lower()
    return s

def qtext_to_hash(qtext):
    h = hashlib.sha256()
    if isinstance(qtext, list):
        key = "\n".join(qtext)
    else:
        key = str(qtext)
    key = key.strip().lower()
    h.update(key.encode("utf-8"))
    return h.hexdigest()

# ---------- Memory CSV helpers ----------
_mem_cache = None
_mem_mtime = None

def ensure_memory_file(path=MEMORY_CSV):
    if not os.path.exists(path):
        os.makedirs(os.path.dirname(path) or ".", exist_ok=True)
        with open(path, "w", newline='', encoding="utf-8") as f:
            writer = csv.writer(f)
            writer.writerow(["mode","question_hash","ts","question_text","computed_answer","chosen_option","chosen_option_norm","correct"])
    return path

def _read_memory_file(path=MEMORY_CSV):
    ensure_memory_file(path)
    rows = []
    try:
        with open(path, "r", newline='', encoding="utf-8") as f:
            reader = csv.DictReader(f)
            for row in reader:
                rows.append(row)
    except Exception:
        pass
    return rows

def load_memory_latest(path=MEMORY_CSV, use_cache=True):
    global _mem_cache, _mem_mtime
    ensure_memory_file(path)
    try:
        mtime = os.path.getmtime(path)
    except Exception:
        mtime = None
    if use_cache and _mem_cache is not None and _mem_mtime == mtime:
        return _mem_cache
    rows = _read_memory_file(path)
    mem = {}
    for row in rows:
        if not row.get("question_hash"):
            continue
        key = (row["mode"], row["question_hash"])
        mem[key] = {
            "ts": row.get("ts"),
            "question_text": row.get("question_text"),
            "computed_answer": row.get("computed_answer"),
            "chosen_option": row.get("chosen_option"),
            "chosen_option_norm": row.get("chosen_option_norm") if row.get("chosen_option_norm") else normalize_choice_text(row.get("chosen_option")),
            "correct": row.get("correct")
        }
    _mem_cache = mem
    _mem_mtime = mtime
    return mem

def lookup_memory_entries(mode, question_lines, path=MEMORY_CSV):
    ensure_memory_file(path)
    qhash = qtext_to_hash(question_lines)
    entries = []
    try:
        with open(path, "r", newline='', encoding="utf-8") as f:
            reader = csv.DictReader(f)
            for row in reader:
                if not row.get("question_hash"):
                    continue
                if row.get("mode") == mode and row.get("question_hash") == qhash:
                    if not row.get("chosen_option_norm"):
                        row["chosen_option_norm"] = normalize_choice_text(row.get("chosen_option"))
                    entries.append(row)
    except Exception:
        pass
    return entries

def append_memory_entry(mode, question_lines, computed_answer, chosen_option, correct_flag, path=MEMORY_CSV):
    ensure_memory_file(path)
    qhash = qtext_to_hash(question_lines)
    ts = datetime.utcnow().isoformat() + "Z"
    chosen_norm = normalize_choice_text(chosen_option)
    try:
        with open(path, "a", newline='', encoding="utf-8") as f:
            writer = csv.writer(f)
            writer.writerow([mode, qhash, ts, "\n".join(question_lines), str(computed_answer), str(chosen_option), chosen_norm, str(correct_flag)])
            f.flush()
            try:
                os.fsync(f.fileno())
            except Exception:
                pass
        global _mem_cache, _mem_mtime
        _mem_cache = None
        _mem_mtime = None
    except Exception as e:
        print("[MEM] error writing memory:", e)

def update_memory_if_better(mode, question_lines, computed_answer, chosen_option, correct_flag, path=MEMORY_CSV):
    mem_latest = load_memory_latest(path, use_cache=False)
    key = (mode, qtext_to_hash(question_lines))
    prev = mem_latest.get(key)
    rank = {"False": 0, "unknown": 1, "True": 2}
    cur_rank = rank.get(str(correct_flag), 1)
    prev_rank = rank.get(str(prev["correct"]), -1) if prev else -1
    if cur_rank >= prev_rank:
        append_memory_entry(mode, question_lines, computed_answer, chosen_option, correct_flag, path)

def pick_true_from_memory(entries):
    for row in reversed(entries):
        if row.get("correct") == "True" and row.get("chosen_option_norm"):
            return row.get("chosen_option_norm")
    return None

def get_proven_false_set(entries):
    s = set()
    for row in entries:
        if row.get("correct") == "False":
            norm = row.get("chosen_option_norm") or normalize_choice_text(row.get("chosen_option"))
            if norm:
                s.add(norm)
    return s

# ---------- Evaluator (unchanged core) ----------
def safe_replace_vars(expr, vars_dict):
    for v, val in vars_dict.items():
        expr = re.sub(rf'\b{re.escape(v)}\b', str(val), expr)
    return expr

def normalize_condition_text(cond):
    return re.sub(r'(?<![=!<>])=(?!=)', '==', cond)

def eval_expr(expr, vars_dict):
    e = safe_replace_vars(expr, vars_dict)
    e = normalize_condition_text(e)
    safe_locals = {}
    if re.search(r'\b(sin|cos|tan|abs|round|min|max|int|float)\b', e):
        import math as _math
        safe_locals.update({'sin': _math.sin, 'cos': _math.cos, 'tan': _math.tan,
                            'abs': abs, 'round': round, 'min': min, 'max': max, 'int': int, 'float': float})
    val = eval(e, {"__builtins__": {}}, safe_locals)
    if isinstance(val, float):
        if abs(val - round(val)) < 1e-9:
            val = int(round(val))
        else:
            val = round(val, 10)
            val = ('{:.10f}'.format(val)).rstrip('0').rstrip('.')
    return val

def parse_assignment(line, vars_dict):
    m = re.match(r'^([A-Za-z_]\w*)\s*(?:<-|←|:=)\s*(.+)$', line)
    if not m:
        return False
    var, rhs = m.groups()
    rhs = rhs.strip()
    if re.match(r'^-?\d+(\.\d+)?$', rhs):
        vars_dict[var] = float(rhs) if '.' in rhs else int(rhs)
        return True
    try:
        val = eval_expr(rhs, vars_dict)
        vars_dict[var] = val
        return True
    except Exception:
        return False

def collect_if_blocks(lines, start_index):
    if_line = lines[start_index]
    cond_m = re.search(r'IF\s+(.+?)\s+THEN', if_line, flags=re.IGNORECASE)
    if cond_m:
        condition = cond_m.group(1).strip()
    else:
        condition = if_line[3:].strip()

    then_lines, else_lines = [], []
    current = 'then'
    i = start_index + 1
    brace_count = 0
    if '{' in if_line:
        brace_count = if_line.count('{') - if_line.count('}')
        remainder = re.sub(r'^.*?{', '', if_line).strip()
        if remainder:
            then_lines.append(remainder)

    while i < len(lines):
        ln = lines[i]
        if re.match(r'^(Apa\b|What\b)', ln, flags=re.IGNORECASE):
            break
        if re.match(r'^ELSE\b', ln, flags=re.IGNORECASE):
            current = 'else'
            if '{' in ln:
                brace_count += ln.count('{') - ln.count('}')
                remainder = re.sub(r'^.*?{', '', ln).strip()
                if remainder:
                    else_lines.append(remainder)
            i += 1
            continue
        if '{' in ln or '}' in ln:
            brace_count += ln.count('{') - ln.count('}')
            cleaned = ln.replace('{', '').replace('}', '').strip()
            if cleaned:
                (then_lines if current == 'then' else else_lines).append(cleaned)
            i += 1
            continue
        (then_lines if current == 'then' else else_lines).append(ln)
        i += 1

    return condition, then_lines, else_lines, i

def execute_block(lines, vars_dict, depth=0):
    outputs = []
    i = 0
    while i < len(lines):
        ln = lines[i].strip()
        if not ln:
            i += 1
            continue
        if re.match(r'^[A-Za-z_]\w*\s*(?:<-|←|:=)', ln):
            parse_assignment(ln, vars_dict)
            i += 1
            continue
        if re.match(r'^IF\b', ln, flags=re.IGNORECASE):
            cond, then_lines, else_lines, next_i = collect_if_blocks(lines, i)
            try:
                cond_eval = eval_expr(normalize_condition_text(cond), vars_dict)
                cond_bool = bool(cond_eval)
            except Exception:
                i = next_i
                continue
            chosen = then_lines if cond_bool else else_lines
            sub = execute_block(chosen, vars_dict, depth + 1)
            outputs.extend(sub)
            i = next_i
            continue
        m = re.search(r'cetak\s*\(\s*(.+?)\s*\)', ln, flags=re.IGNORECASE)
        if m:
            expr = m.group(1).strip()
            try:
                val = eval_expr(expr, vars_dict)
                outputs.append(str(val))
            except Exception:
                pass
            i += 1
            continue
        m2 = re.search(r'cetak\s+(.+)', ln, flags=re.IGNORECASE)
        if m2:
            expr = m2.group(1).strip()
            try:
                val = eval_expr(expr, vars_dict)
                outputs.append(str(val))
            except Exception:
                pass
            i += 1
            continue
        i += 1
    return outputs

def solve_question_outputs(question_text):
    """Return the list of outputs produced by the question's code (one element per 'cetak')."""
    lines = normalize_text(question_text)
    if not lines:
        return []
    vars_dict = {}
    outputs = execute_block(lines, vars_dict)
    return outputs  # list of strings (possibly empty)

# ---------- Option parsing & matching ----------
NUM_RE = re.compile(r'[-+]?\d+(\.\d+)?')
INT_RE = re.compile(r'^-?\d+$')
FRAC_SLASH_RE = re.compile(r'^\s*-?\d+\s*/\s*-?\d+\s*$')

def parse_option_to_tokens(opt_str):
    if opt_str is None:
        return []
    s = opt_str.replace('\xa0', ' ').strip()
    s = re.sub(r'[(),;]', ' ', s)
    s = re.sub(r'[?"\']', '', s)
    s = re.sub(r'\s+', ' ', s).strip()
    tokens = s.split(' ')
    return tokens

def token_to_number(tok):
    if tok is None:
        return None
    tok = tok.strip()
    if INT_RE.match(tok):
        return int(tok)
    if FRAC_SLASH_RE.match(tok):
        a,b = tok.split('/')
        try:
            return Fraction(int(a.strip()), int(b.strip()))
        except Exception:
            return None
    try:
        f = float(tok)
        return f
    except Exception:
        return None

def option_string_to_number_forms(opt_str):
    tokens = parse_option_to_tokens(opt_str)
    numbers = []
    for t in tokens:
        num = token_to_number(t)
        numbers.append(num)
    fraction_values = []
    if len(tokens) == 2 and all(INT_RE.match(t) for t in tokens):
        try:
            n = int(tokens[0]); d = int(tokens[1])
            if d != 0:
                fraction_values.append(Fraction(n, d))
        except Exception:
            pass
    return {"tokens": tokens, "numbers": numbers, "fractions": fraction_values}

def float_to_fraction_variants(val):
    variants = set()
    try:
        frac = Fraction(val).limit_denominator(1000)
        variants.add(frac)
        variants.add((frac.numerator, frac.denominator))
    except Exception:
        pass
    return variants

def try_parse_computed_as_numbers(comp):
    toks = parse_option_to_tokens(comp)
    nums = []
    for t in toks:
        n = token_to_number(t)
        nums.append(n)
    return nums

def try_numeric_match_between(a, b, tol=1e-9):
    try:
        if isinstance(a, Fraction) and isinstance(b, Fraction):
            return a == b
        if isinstance(a, Fraction) and isinstance(b, (int, float)):
            return abs(float(a) - float(b)) <= tol
        if isinstance(b, Fraction) and isinstance(a, (int, float)):
            return abs(float(b) - float(a)) <= tol
        return math.isclose(float(a), float(b), rel_tol=1e-9, abs_tol=tol)
    except Exception:
        return False

def option_matches_answer(option_value_raw, computed_answer):
    if option_value_raw is None:
        return False

    opt_raw = option_value_raw.replace('\xa0', ' ').strip()
    comp_raw = str(computed_answer).replace('\xa0', ' ').strip()

    def norm(s): return re.sub(r'\s+', ' ', s.strip())

    if norm(opt_raw) == norm(comp_raw):
        return True

    opt_info = option_string_to_number_forms(opt_raw)
    comp_tokens = parse_option_to_tokens(comp_raw)
    comp_numbers = try_parse_computed_as_numbers(comp_raw)

    if len(comp_numbers) == len(opt_info["numbers"]) and len(comp_numbers) > 0:
        all_ok = True
        for cn, on in zip(comp_numbers, opt_info["numbers"]):
            if cn is None or on is None:
                all_ok = False
                break
            if not try_numeric_match_between(cn, on):
                all_ok = False
                break
        if all_ok:
            return True

    if len(opt_info["tokens"]) == 2 and all(INT_RE.match(t) for t in opt_info["tokens"]):
        try:
            n = int(opt_info["tokens"][0]); d = int(opt_info["tokens"][1])
        except Exception:
            n = None; d = None
        if n is not None and d != 0:
            opt_frac = Fraction(n, d)
            if len(comp_numbers) == 1 and comp_numbers[0] is not None:
                if try_numeric_match_between(float(opt_frac), float(comp_numbers[0])):
                    return True
            if len(comp_tokens) == 1:
                tok0 = comp_tokens[0] if isinstance(comp_tokens[0], str) else ''
                if FRAC_SLASH_RE.match(tok0):
                    try:
                        a, b = tok0.split('/')
                        if Fraction(int(a), int(b)) == opt_frac:
                            return True
                    except Exception:
                        pass

    for on in opt_info["numbers"]:
        if isinstance(on, Fraction):
            for cn in comp_numbers:
                if cn is None:
                    continue
                try:
                    if try_numeric_match_between(float(on), float(cn)):
                        return True
                except Exception:
                    continue

    for cn in comp_numbers:
        if isinstance(cn, float):
            fr_variants = float_to_fraction_variants(cn)
            for v in fr_variants:
                if isinstance(v, Fraction):
                    if len(opt_info["tokens"]) == 2 and all(INT_RE.match(t) for t in opt_info["tokens"]):
                        try:
                            if int(opt_info["tokens"][0]) == v.numerator and int(opt_info["tokens"][1]) == v.denominator:
                                return True
                        except Exception:
                            pass
                    if any(tok == f"{v.numerator}/{v.denominator}" for tok in opt_info["tokens"]):
                        return True
                    for on in opt_info["numbers"]:
                        if on is None:
                            continue
                        if try_numeric_match_between(float(v), float(on)):
                            return True
                elif isinstance(v, tuple) and len(v) == 2:
                    n, d = v
                    if len(opt_info["tokens"]) == 2 and all(INT_RE.match(t) for t in opt_info["tokens"]):
                        try:
                            if int(opt_info["tokens"][0]) == n and int(opt_info["tokens"][1]) == d:
                                return True
                        except Exception:
                            pass

    if len(opt_info["tokens"]) >= 2 and len(comp_numbers) >= 2:
        all_ok = True
        for cn, on in zip(comp_numbers, list(reversed(opt_info["numbers"]))):
            if cn is None or on is None or not try_numeric_match_between(cn, on):
                all_ok = False
                break
        if all_ok:
            return True

    for cn in comp_numbers:
        if isinstance(cn, float):
            for prec in (0, 1, 2, 3):
                try:
                    rounded = round(cn, prec)
                except Exception:
                    continue
                for on in opt_info["numbers"]:
                    if on is None:
                        continue
                    if isinstance(on, int) and try_numeric_match_between(rounded, float(on)):
                        return True
    return False

# ---------- Deterministic correctness detection ----------
async def detect_correctness_after_selection(page, timeout=0.5):
    try:
        await asyncio.sleep(timeout)
        el_benar = await page.query_selector(".feedback.benar")
        if el_benar:
            txt = (await el_benar.inner_text()).strip().lower()
            if "jawaban benar" in txt or "benar" in txt:
                return "True"
            return "True"
        el_salah = await page.query_selector(".feedback.salah")
        if el_salah:
            txt = (await el_salah.inner_text()).strip().lower()
            if "jawaban salah" in txt or "salah" in txt:
                return "False"
            return "False"
        content = await page.content()
        if "jawaban benar" in content.lower() or "🎉" in content:
            return "True"
        if "jawaban salah" in content.lower() or "😢" in content:
            return "False"
    except Exception:
        pass
    return "unknown"

# ---------- New: answer variant generation & scoring ----------
def generate_variants_from_outputs(outputs):
    """
    Given list of outputs from solve_question_outputs, produce prioritized variants.
    Returns list of strings (variants) in priority order.
    """
    variants = []
    seen = set()

    def push(v):
        if v is None:
            return
        s = str(v).strip()
        if not s:
            return
        key = re.sub(r'\s+', ' ', s).lower()
        if key in seen:
            return
        seen.add(key)
        variants.append(s)

    # each output as-is (preserve order)
    for out in outputs:
        push(out)

    # punctuation-stripped variants + lowercased simplified
    for out in outputs:
        stripped = re.sub(r'[^\w/ -]', '', out).strip()
        push(stripped)

    # numeric variants: if any output is numeric-ish, add integer and fraction forms
    for out in outputs:
        try:
            f = float(str(out))
            # if almost integer -> integer
            if abs(f - round(f)) < 1e-9:
                push(str(int(round(f))))
            # fraction variants
            frs = float_to_fraction_variants(f)
            for fr in frs:
                if isinstance(fr, Fraction):
                    push(f"{fr.numerator}/{fr.denominator}")
        except Exception:
            pass

    # also add concatenated outputs (if multiple outputs form multi-part answers)
    if len(outputs) > 1:
        push(" ".join(outputs))
        push(" ".join([re.sub(r'[^\w/ -]','',o).strip() for o in outputs]))

    return variants

def score_option_against_answer(option_display, answer_variant):
    """
    Deterministic score: numeric closeness if both numeric, else SequenceMatcher ratio of normalized strings.
    Return float score where higher is better.
    """
    opt_norm = option_display.strip()
    ans_norm = str(answer_variant).strip()

    # numeric attempts
    opt_nums = try_parse_computed_as_numbers(opt_norm)
    ans_nums = try_parse_computed_as_numbers(ans_norm)

    # If both parse to single numeric, use inverse distance
    if len(opt_nums) == 1 and len(ans_nums) == 1 and opt_nums[0] is not None and ans_nums[0] is not None:
        try:
            diff = abs(float(opt_nums[0]) - float(ans_nums[0]))
            # convert to score: smaller diff => higher score
            return 1.0 / (1.0 + diff)
        except Exception:
            pass

    # else use fuzzy text similarity on normalized forms
    a = normalize_choice_text(opt_norm)
    b = normalize_choice_text(ans_norm)
    return difflib.SequenceMatcher(None, a, b).ratio()

def pick_best_non_false_by_scoring(candidates, proven_false_set, answer_variants):
    """
    candidates: list of tuples (radio_handle, display_raw, normalized)
    answer_variants: prioritized list of answer strings
    Return chosen candidate tuple or None.
    Deterministically computes scores and picks highest-scoring candidate not in proven_false_set.
    """
    best = None
    best_score = -1.0
    for r, display, norm in candidates:
        if norm in proven_false_set:
            continue
        # compute best score across variants (prefer earlier variants by small bonus)
        score = 0.0
        for idx, var in enumerate(answer_variants):
            s = score_option_against_answer(display, var)
            # apply small variant decay so earlier variants slightly favored
            weighted = s * (1.0 / (1 + idx * 0.2))
            if weighted > score:
                score = weighted
        # tie-breaker deterministic: lower lexicographic normalized text wins (to avoid randomness)
        tie_key = (score, -1.0 * float(hash(norm) % 100000) / 100000.0)  # deterministic-ish
        if score > best_score:
            best_score = score
            best = (r, display, norm, score)
    return best  # tuple or None

# ---------- Worker (main loop) ----------
async def worker_loop(playwright, mode, wid):
    restarts = 0
    while True:
        if MAX_RESTARTS_PER_WORKER is not None and restarts >= MAX_RESTARTS_PER_WORKER:
            print(f"[W{wid}][{mode}] reached max restarts ({MAX_RESTARTS_PER_WORKER}). Exiting.")
            return

        browser = None
        try:
            browser = await playwright.chromium.launch(headless=HEADLESS)
            context = await browser.new_context()
            page = await context.new_page()

            # login + select quiz (adapt to your site)
            try:
                await page.goto("https://sujaini.my.id/quiz/login", wait_until="networkidle", timeout=NAV_TIMEOUT)
                await page.fill("input[name='username']", "INSERT NIM HERE")
                await page.click("button[type='submit']")
                await asyncio.sleep(0.4)
                try:
                    await page.wait_for_selector(".quiz-link", timeout=2000)
                    desired = mode.upper()
                    target = await page.query_selector(f'a.quiz-link:has-text("{desired}")')
                    if target:
                        await target.click()
                        await page.wait_for_selector(".soal", timeout=QUESTION_TIMEOUT)
                except PlaywrightTimeoutError:
                    await page.wait_for_selector(".soal", timeout=QUESTION_TIMEOUT)
            except Exception as e:
                print(f"[W{wid}][{mode}] login error: {e}")
                try:
                    await browser.close()
                except Exception:
                    pass
                restarts += 1
                await asyncio.sleep(RESTART_DELAY_S)
                continue

            # question loop
            while True:
                try:
                    cur_url = page.url
                    if "/quiz/hasil" in cur_url:
                        try:
                            await browser.close()
                        except Exception:
                            pass
                        restarts += 1
                        await asyncio.sleep(RESTART_DELAY_S)
                        break

                    await page.wait_for_selector(".soal", timeout=QUESTION_TIMEOUT)
                    qel = await page.query_selector(".soal")
                    question_text = await qel.inner_text()
                    question_lines = normalize_text(question_text)
                    qhash = qtext_to_hash(question_lines)
                    key = (mode, qhash)

                    # load memory and entries for this question
                    mem_latest = load_memory_latest(MEMORY_CSV, use_cache=True)
                    all_entries = lookup_memory_entries(mode, question_lines)
                    proven_true_norm = pick_true_from_memory(all_entries)
                    proven_false_set = get_proven_false_set(all_entries)

                    # collect options
                    radios = await page.query_selector_all("input[name='jawaban']")
                    candidates = []
                    for r in radios:
                        val = await (await r.get_property("value")).json_value()
                        # attempt to get label text if exists
                        parent = await r.evaluate_handle("el => el.closest('label')")
                        lbl = None
                        if parent:
                            try:
                                lbl = await (await parent.get_property("innerText")).json_value()
                            except Exception:
                                lbl = None
                        display = str(lbl or val or "").strip()
                        candidates.append((r, display, normalize_choice_text(display)))

                    # 0) If proven-True exists try to match it exactly (highest priority)
                    if proven_true_norm:
                        for r, display, norm in candidates:
                            if norm == proven_true_norm:
                                await r.check()
                                chosen_display = display
                                # submit
                                btn = await page.query_selector(".btn-next")
                                if btn:
                                    await btn.click()
                                else:
                                    fb = await page.query_selector("button[name='selesai']")
                                    if fb:
                                        await fb.click()
                                correctness = await detect_correctness_after_selection(page)
                                update_memory_if_better(mode, question_lines, proven_true_norm, chosen_display, correctness)
                                await asyncio.sleep(0.35)
                                raise EOFError("continue_loop")  # trick to jump to outer loop continue
                    # 1) compute outputs and generate variants
                    outputs = solve_question_outputs(question_text)
                    variants = generate_variants_from_outputs(outputs)
                    # also include joined outputs as last resort
                    if not variants:
                        variants = [""]

                    # 2) Try to find option that matches any variant while NOT in proven_false_set
                    matched_candidate = None
                    for var in variants:
                        for r, display, norm in candidates:
                            if norm in proven_false_set:
                                continue
                            if option_matches_answer(display, var) or normalize_choice_text(display) == normalize_choice_text(var):
                                matched_candidate = (r, display, norm, var)
                                break
                        if matched_candidate:
                            break

                    # 3) Edge case: best variant maps to an option that *is* proven-false.
                    #    In that case: do NOT select it — instead try next variants or scoring.
                    if not matched_candidate:
                        # maybe the computed best variant maps only to proven false; try scoring method to pick best non-false
                        scored = pick_best_non_false_by_scoring(candidates, proven_false_set, variants)
                        if scored:
                            r, display, norm, score = scored
                            matched_candidate = (r, display, norm, f"scored(score={score:.4f})")

                    # 4) If still nothing matched, fall back to simple elimination:
                    if not matched_candidate:
                        remaining = [(r, d, n) for (r, d, n) in candidates if n not in proven_false_set]
                        if len(remaining) == 1:
                            r, display, norm = remaining[0]
                            matched_candidate = (r, display, norm, "only_remaining")
                        elif len(remaining) > 1:
                            # pick highest similarity between candidate and first variant (deterministic)
                            bestsim = -1.0
                            bestc = None
                            for r, display, norm in remaining:
                                sim = difflib.SequenceMatcher(None, normalize_choice_text(display), normalize_choice_text(variants[0])).ratio()
                                if sim > bestsim:
                                    bestsim = sim
                                    bestc = (r, display, norm)
                            if bestc:
                                r, display, norm = bestc
                                matched_candidate = (r, display, norm, f"sim({bestsim:.3f})")
                        else:
                            # everything is proven false (rare). choose the proven-True for another question? No.
                            # Last resort: choose first option (deterministic)
                            if candidates:
                                r, display, norm = candidates[0]
                                matched_candidate = (r, display, norm, "force_first")

                    # finally select matched_candidate
                    if matched_candidate:
                        r, display, norm, reason = matched_candidate
                        # Before clicking, ensure we are not about to select a proven-false (defensive)
                        if norm in proven_false_set:
                            # Defensive: this should not happen because we avoided proven-false above
                            # but if it does, try to pick next best non-false via scoring
                            scored = pick_best_non_false_by_scoring(candidates, proven_false_set, variants)
                            if scored:
                                r, display, norm, score = scored
                                reason = f"rescored(score={score:.4f})"
                        # check the radio
                        await r.check()
                        # submit
                        btn = await page.query_selector(".btn-next")
                        if btn:
                            await btn.click()
                        else:
                            fb = await page.query_selector("button[name='selesai']")
                            if fb:
                                await fb.click()

                        # detect correctness and store memory
                        correctness = await detect_correctness_after_selection(page)
                        update_memory_if_better(mode, question_lines, outputs or "", display, correctness)
                        # small pause
                        await asyncio.sleep(0.35)
                        # continue outer loop
                        continue

                except EOFError:
                    # used to simulate "continue" when selecting proven-True early
                    continue
                except PlaywrightTimeoutError:
                    # recover by restarting
                    try:
                        await browser.close()
                    except Exception:
                        pass
                    restarts += 1
                    await asyncio.sleep(RESTART_DELAY_S)
                    break
                except KeyboardInterrupt:
                    try:
                        if browser:
                            await browser.close()
                    except Exception:
                        pass
                    return
                except Exception as e:
                    print(f"[W{wid}][{mode}] session exception: {e}")
                    traceback.print_exc()
                    try:
                        if browser and browser.is_connected:
                            await browser.close()
                    except Exception:
                        pass
                    restarts += 1
                    await asyncio.sleep(RESTART_DELAY_S)
                    break

        except Exception as exc_outer:
            print(f"[W{wid}][{mode}] outer exception: {exc_outer}")
            traceback.print_exc()
            try:
                if browser:
                    await browser.close()
            except Exception:
                pass
            restarts += 1
            await asyncio.sleep(RESTART_DELAY_S)
            continue

# ---------- Orchestrator ----------
async def main():
    print(f"[MAIN] starting workers: runtunan={WORKERS.get('runtunan',0)}, percabangan={WORKERS.get('percabangan',0)}")
    async with async_playwright() as playwright:
        tasks = []
        wid = 0
        for mode, count in WORKERS.items():
            for _ in range(count):
                wid += 1
                tasks.append(asyncio.create_task(worker_loop(playwright, mode, wid)))
        try:
            await asyncio.gather(*tasks)
        except asyncio.CancelledError:
            pass
        except KeyboardInterrupt:
            for t in tasks:
                t.cancel()
            await asyncio.gather(*tasks, return_exceptions=True)

if __name__ == "__main__":
    try:
        asyncio.run(main())
    except KeyboardInterrupt:
        print("Interrupted. Exiting.")
        try:
            sys.exit(0)
        except SystemExit:
            pass
