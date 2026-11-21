#!/usr/bin/env python3
"""Independent finite checks for the Unifier.
Standard library only; exact integer and rational arithmetic throughout.
Rounding is round(y) = floor(y + 1/2), as in the paper.
x mod n denotes the remainder in [0, n), which is Python's % for n > 0.
Author: lmtlssss🜐. License: MIT.
"""
import json
import math
import sys
from fractions import Fraction as Q
from itertools import product
from pathlib import Path

RESULTS = []


def report(sid, ok, detail):
    RESULTS.append({"id": sid, "pass": bool(ok), "detail": detail})
    print(f"{sid:<4} {'pass' if ok else 'FAIL'}  {detail}")


def run(sid, fn):
    try:
        ok, detail = fn()
    except Exception as exc:  # a crash is a failure, never a pass
        ok, detail = False, f"exception {type(exc).__name__}: {exc}"
    report(sid, ok, detail)


def rnd(y):
    return math.floor(y + Q(1, 2))


def clog(b, m):
    """Least L with b**L >= m."""
    L, p = 0, 1
    while p < m:
        p *= b
        L += 1
    return L


# ---------------------------------------------------------------- section 1
def t3():
    for h in range(0, 9):
        if sum(1 for _ in product(range(3), repeat=h)) != 3 ** h:
            return False, f"count at h={h}"
    for h in range(0, 200):
        if clog(3, 3 ** h) != h:
            return False, f"clog at h={h}"
        if h >= 1 and 3 ** (h - 1) >= 3 ** h:
            return False, "order"
    return True, "3^h keys for h<=8 by enumeration; clog 3 (3^h) = h for h<200"


# ---------------------------------------------------------------- section 3
def native(a, b):
    return 2 * a * b


def t5():
    if native(1, 1) != 2:
        return False, "1 (x) 1"
    for a, b in product((0, 1), repeat=2):
        if a + b != (a ^ b) + native(a, b):
            return False, f"bits {a},{b}"
    n = 0
    for a in range(201):
        for b in range(201):
            if (a + b) ** 2 != a * a + b * b + native(a, b):
                return False, f"square {a},{b}"
            if native(a, b) // 2 != a * b or native(a, b) % 2:
                return False, f"half {a},{b}"
            n += 1
    return True, f"1(x)1=2; 4 bit pairs; square and half-normalization on {n} pairs"


LEGAL = [(s, w) for s in (0, 1) for w in (0, 1) if not (s == 0 and w == 1)]


def decode_trit(t):
    return (int(t >= 1), int(t >= 2))


def t6():
    if sorted(s + w for s, w in LEGAL) != [0, 1, 2] or len(LEGAL) != 3:
        return False, "image"
    if any(decode_trit(s + w) != (s, w) for s, w in LEGAL):
        return False, "left inverse"
    if any(sum(decode_trit(t)) != t for t in range(3)):
        return False, "right inverse"
    if any(decode_trit(t) == (0, 1) for t in range(3)):
        return False, "corner"
    return True, "3 legal pairs onto {0,1,2}; inverse t->(t>=1,t>=2); corner (0,1) never decoded"


def t7():
    total = 0
    for L in range(0, 7):
        keys = list(product(range(3), repeat=L))
        enc = {k: sum(t * 3 ** i for i, t in enumerate(k)) for k in keys}
        if sorted(enc.values()) != list(range(3 ** L)):
            return False, f"bijection L={L}"
        for idx in range(3 ** L):
            k, v = [], idx
            for _ in range(L):
                v, r = divmod(v, 3)
                k.append(r)
            if enc[tuple(k)] != idx:
                return False, f"decoder L={L} idx={idx}"
        total += len(keys)
    return True, f"L=0..6, {total} keys, upper decoder and lower encoder mutually inverse"


# ---------------------------------------------------------------- section 4
# step codes: 0 = or 0, 1 = or 1, 2 = and 0, 3 = and 1
STEPS = [("or", 0), ("or", 1), ("and", 0), ("and", 1)]
MAXW = 12


def pack(f0, f1, e, p):
    return f0 | f1 << 1 | e << 2 | p << 3


def unpack(s):
    return s & 1, s >> 1 & 1, s >> 2 & 1, s >> 3 & 1


def step_table(op, v):
    t = bytearray([255] * 256)
    for s in range(16):
        f0, f1, e, p = unpack(s)
        if op == "or":
            t[s] = pack(v | f0, v | f1, e | v, p)
        else:
            t[s] = pack(v & f0, v & f1, e, p & v)
    return bytes(t)


def build_windows():
    """st[L][code] is (F_S(0), F_S(1), E_S, P_S) for the window S of length L
    whose base-4 digits, most significant first, are its steps from the top.
    Built from the definition F_(h::S)(R) = h(F_S(R))."""
    tables = [step_table(op, v) for op, v in STEPS]
    proj = bytes([s & 3 if s < 16 else 255 for s in range(256)])
    cur = bytes([pack(0, 1, 0, 1)])
    st_present, fn = [], []
    for L in range(MAXW + 1):
        if L:
            cur = b"".join(cur.translate(tables[h]) for h in range(4))
        st_present.append([v for v in range(256) if cur.find(bytes([v])) != -1])
        fn.append(cur.translate(proj))
    return st_present, fn


def direct_F(window, R):
    r = R
    for op, v in reversed(window):
        r = (v | r) if op == "or" else (v & r)
    return r


def window_of(L, code):
    digits = []
    for _ in range(L):
        code, d = divmod(code, 4)
        digits.append(d)
    return [STEPS[d] for d in reversed(digits)]


WIN = {}


def windows():
    if not WIN:
        WIN["st"], WIN["fn"] = build_windows()
        # cross-check the tables against direct folding for L <= 6
        for L in range(7):
            for code in range(4 ** L):
                w = window_of(L, code)
                f = WIN["fn"][L][code]
                if (f & 1, f >> 1) != (direct_F(w, 0), direct_F(w, 1)):
                    raise AssertionError(f"table mismatch L={L} code={code}")
    return WIN


def count_windows():
    return sum(4 ** L for L in range(MAXW + 1))


def t8():
    W = windows()
    for L, present in enumerate(W["st"]):
        for s in present:
            f0, f1, _, _ = unpack(s)
            if not f0 <= f1:
                return False, f"monotone L={L}"
            for R in (0, 1):
                if (f0, f1)[R] != (f0 | (f1 & R)):
                    return False, f"normal form L={L}"
            t = f1 + f0
            if (t == 0 and (f0, f1) != (0, 0)) or (t == 1 and (f0, f1) != (0, 1)) \
                    or (t == 2 and (f0, f1) != (1, 1)):
                return False, f"trit meaning L={L}"
    return True, f"every window of length 0..{MAXW}: {count_windows()} windows"


def compose(f, g):
    """code of F_S after F_S' from codes f0 + 2 f1."""
    fv = (f & 1, f >> 1)
    return fv[g & 1] | fv[g >> 1] << 1


def trit(f):
    return (f & 1) + (f >> 1)


def cmap(t, u):
    return u if t == 1 else t


def t9():
    W = windows()
    fn = W["fn"]
    post = {f: bytes([compose(f, g) if g < 4 else 255 for g in range(256)]) for f in range(4)}
    pre = {g: bytes([compose(f, g) if f < 4 else 255 for f in range(256)]) for g in range(4)}
    pairs = 0
    for L in range(MAXW + 1):
        for a in range(L + 1):
            b = L - a
            if a <= b:
                for cs in range(4 ** a):
                    lo = cs * 4 ** b
                    if fn[L][lo:lo + 4 ** b] != fn[b].translate(post[fn[a][cs]]):
                        return False, f"concatenation L={L} a={a}"
            else:
                for cp in range(4 ** b):
                    if fn[L][cp::4 ** b] != fn[a].translate(pre[fn[b][cp]]):
                        return False, f"concatenation L={L} a={a}"
            pairs += 4 ** L
    legal = (0b00, 0b10, 0b11)
    for f, g in product(legal, repeat=2):
        if trit(compose(f, g)) != cmap(trit(f), trit(g)):
            return False, "trit composition"
    for t, u, v in product(range(3), repeat=3):
        if cmap(cmap(t, u), v) != cmap(t, cmap(u, v)):
            return False, "associativity"
    if any(cmap(1, t) != t or cmap(t, 1) != t for t in range(3)):
        return False, "identity"
    return True, (f"F_(S++S') = F_S o F_S' on all {pairs} concatenations of total "
                  f"length <= {MAXW}; c associative with identity 1")


def t10():
    W = windows()
    for L, present in enumerate(W["st"]):
        for s in present:
            f0, f1, e, p = unpack(s)
            for R in (0, 1):
                fR = (f0, f1)[R]
                if fR != (f0 | (p & R)) or fR != (f1 & (e | R)):
                    return False, f"normal forms L={L}"
    # direct E and P on short windows, independent of the tables
    for L in range(7):
        for code in range(4 ** L):
            w = window_of(L, code)
            e = int(any(v for op, v in w if op == "or"))
            p = int(all(v for op, v in w if op == "and"))
            for R in (0, 1):
                fR = direct_F(w, R)
                if fR != (direct_F(w, 0) | (p & R)) or fR != (direct_F(w, 1) & (e | R)):
                    return False, f"direct L={L}"
    return True, f"both normal forms on every window of length 0..{MAXW}, R in {{0,1}}"


def t11():
    states = list(product((0, 1), repeat=2))
    obs = {(g, p): tuple(g | (p & R) for R in (0, 1)) for g, p in states}
    classes = set(obs.values())
    if len(classes) != 3:
        return False, f"{len(classes)} classes"
    for bmap in product((0, 1), repeat=4):
        b = dict(zip(states, bmap))
        if all(obs[x] == obs[y] for x in states for y in states if b[x] == b[y]):
            return False, "a one-bit retained boundary exists"
    rails = {x: (obs[x][1], obs[x][0]) for x in states}
    if set(rails.values()) != {(0, 0), (1, 0), (1, 1)}:
        return False, "rails"
    if any((rails[x] == rails[y]) != (obs[x] == obs[y]) for x in states for y in states):
        return False, "rails not exact"
    return True, "3 classes; none of the 16 maps into one bit is a retained boundary; rails miss only (0,1)"


# ---------------------------------------------------------------- section 5
def instances():
    out = []
    for k in (1, 2, 3):
        for ns in product(range(1, 31), repeat=k):
            if list(ns) != sorted(set(ns)):
                continue
            for eps in product((1, -1), repeat=k):
                s = sum(Q(e, n) for e, n in zip(eps, ns))
                if s > 0 and s.numerator == 1:
                    out.append((s.denominator, ns, eps))
    return out


INST = []


def inst():
    if not INST:
        INST.extend(instances())
    return INST


def t12():
    checked = 0
    det = 0
    for N, ns, eps in inst():
        if any(N % n for n in ns):
            continue
        c = [e * (N // n) for e, n in zip(eps, ns)]
        if sum(c) != 1:
            return False, f"sum c_i at {N},{ns}"
        for x in range(-60, 61):
            for j in (-1, 0, 2):
                a = [x % n + j * n for n in ns]
                if (sum(ci * ai for ci, ai in zip(c, a)) - x) % N:
                    return False, f"congruence N={N} ns={ns} x={x}"
                checked += 1
        if N <= 1000:
            seen = {}
            for x in range(N):
                key = tuple(x % n for n in ns)
                if key in seen:
                    return False, f"residues not injective N={N}"
                seen[key] = x
            det += 1
    # general form: every pair of integer coefficients in [-N, N) with
    # N | c_i n_i and c_1 + c_2 = 1 (mod N), for N <= 24 and divisors n_1 < n_2
    general = 0
    for N in range(1, 25):
        divs = [d for d in range(1, N + 1) if N % d == 0]
        for n1, n2 in product(divs, repeat=2):
            if n1 >= n2:
                continue
            for c1, c2 in product(range(-N, N), repeat=2):
                if (c1 * n1) % N or (c2 * n2) % N or (c1 + c2 - 1) % N:
                    continue
                for x in range(-N, N):
                    for j in (-1, 0, 1):
                        a1, a2 = x % n1 + j * n1, x % n2 - j * n2
                        if (c1 * a1 + c2 * a2 - x) % N:
                            return False, f"general form N={N} c=({c1},{c2})"
                general += 1
    return True, (f"{checked} congruences; residue tuple injective mod N on {det} instances; "
                  f"general form on {general} coefficient pairs, N<=24")


def t13():
    n_inst = 0
    nondiv = 0
    for N, ns, eps in inst():
        n_inst += 1
        nondiv += any(N % n for n in ns)
        for x in range(-60, 61):
            m = Q(x, N) - sum(e * Q(x % n, n) for e, n in zip(eps, ns))
            if m.denominator != 1:
                return False, f"N={N} ns={ns} x={x}"
    return True, f"{n_inst} decompositions 1/N = sum eps_i/n_i with n_i<=30 ({nondiv} without n_i | N), x in [-60,60]"


def t14():
    for x in range(-1000, 1001):
        if (4 * (x % 3) - 3 * (x % 4) - x) % 12:
            return False, f"zodiac x={x}"
    cnt = 0
    for n in range(1, 201):
        M = n * (n + 1)
        for x in range(-300, 301):
            if ((n + 1) * (x % n) - n * (x % (n + 1)) - x) % M:
                return False, f"n={n} x={x}"
            cnt += 1
    return True, f"x mod 12 for x in [-1000,1000]; n(n+1) family for n<=200, {cnt} cases"


def t15():
    K = 8
    cnt = 0
    for n in range(1, 41):
        for a in range(-n, 2 * n + 1):
            for j in range(-K + 1, K):
                th = Q(a, n) + Q(j, 2 * n * K)
                if rnd(n * th) != a:
                    return False, f"reader n={n} a={a} j={j}"
                cnt += 1
    comp = 0
    for N, ns, eps in inst():
        if any(N % n for n in ns) or len(ns) < 2 or N > 240:
            continue
        beta = Q(1, 2 * (max(ns) + min(ns)))
        if not all(beta < Q(1, 2 * n) for n in ns):
            return False, "bound not below a dial tolerance"
        grid = [-beta * Q(99, 100), -beta / 2, Q(0), beta / 2, beta * Q(99, 100)]
        if len(ns) == 3:
            grid = [-beta * Q(99, 100), Q(0), beta * Q(99, 100)]
        c = [e * (N // n) for e, n in zip(eps, ns)]
        for x in range(min(N, 48)):
            for err in product(grid, repeat=len(ns)):
                a = [rnd(n * (Q(x % n, n) + d)) % n for n, d in zip(ns, err)]
                if (sum(ci * ai for ci, ai in zip(c, a)) - x) % N:
                    return False, f"composed reading N={N} ns={ns} x={x}"
                comp += 1
    return True, f"{cnt} single-dial readings; {comp} composed readings with error < 1/(2(nmax+nmin))"


def t16():
    K = 8
    cnt = 0
    for N in range(1, 61):
        for x in range(-30, 31):
            for j in range(-K + 1, K):
                if rnd(N * (Q(x, N) + Q(j, 2 * N * K))) != x:
                    return False, f"N={N} x={x}"
                cnt += 1
            if rnd(N * (Q(x, N) + Q(1, 2 * N))) != x + 1:
                return False, f"half step N={N} x={x}"
    return True, f"{cnt} readings with |d|<1/(2N); d=1/(2N) gives x+1 for all N<=60"


# ---------------------------------------------------------------- section 6
def quarter(q, x, y, s):
    if q == 0:
        return (y, x)
    if q == 1:
        return (x, y + s)
    if q == 2:
        return (x + s, y + s)
    return (2 * s - 1 - y, s - 1 - x)


def hilbert_point(k, d):
    """Top-down evaluation: the leading base-4 digit selects the quarter."""
    if k == 0:
        return (0, 0)
    q, r = divmod(d, 4 ** (k - 1))
    x, y = hilbert_point(k - 1, r)
    return quarter(q, x, y, 2 ** (k - 1))


def t17_19():
    H = [[(0, 0)]]
    for k in range(8):
        s = 2 ** k
        H.append([quarter(q, x, y, s) for q in range(4) for (x, y) in H[k]])
    res = {}
    for k in range(9):
        side = 2 ** k
        pts = H[k]
        ok17 = len(pts) == 4 ** k and set(pts) == set(product(range(side), repeat=2))
        ok18 = all(abs(a[0] - b[0]) + abs(a[1] - b[1]) == 1 for a, b in zip(pts, pts[1:]))
        ok19 = pts[0] == (0, 0) and pts[-1] == (side - 1, 0)
        ok19 = ok19 and all(pts[d] == hilbert_point(k, d) for d in range(4 ** k))
        if not (ok17 and ok18 and ok19):
            return {"T17": (ok17, f"k={k}"), "T18": (ok18, f"k={k}"), "T19": (ok19, f"k={k}")}
        res[k] = True
    n = sum(4 ** k for k in range(9))
    return {"T17": (True, f"bijection onto the 2^k grid for k=0..8 ({n} cells)"),
            "T18": (True, f"consecutive cells at distance exactly 1 in one coordinate, k=0..8"),
            "T19": (True, "quarter equalities against top-down evaluation k<=8; H_k(0)=(0,0), H_k(4^k-1)=(2^k-1,0) k<=8")}


# ---------------------------------------------------------------- section 7
def t21():
    for m in range(1, 244):
        L = clog(3, m)
        if 3 ** L < m or (L > 0 and 3 ** (L - 1) >= m):
            return False, f"clog m={m}"
        X = range(2 * m + 1)
        f = {x: x % m for x in X}
        g = {}
        for x in X:
            v, key = f[x], []
            for _ in range(L):
                v, r = divmod(v, 3)
                key.append(r)
            g[x] = tuple(key)
        h = {key: sum(t * 3 ** i for i, t in enumerate(key)) for key in set(g.values())}
        if any(h[g[x]] != f[x] for x in X):
            return False, f"factorization m={m}"
    cnt = 0
    for m1 in range(1, 121):
        for m2 in range(1, 121):
            c1, c2, c12 = clog(3, m1), clog(3, m2), clog(3, m1 * m2)
            if not (c12 <= c1 + c2 <= c12 + 1):
                return False, f"(c) m1={m1} m2={m2}"
            cnt += 1
    return True, f"(a),(b) for m<=243; (c) for {cnt} pairs of range sizes m1,m2<=120"


def t23():
    cnt = 0
    for n in range(1, 65):
        def rho(th):
            return Q(rnd(n * th), n)
        for j in range(-16 * n, 16 * n + 1):
            th = Q(j, 8 * n)
            if rho(rho(th)) != rho(th):
                return False, f"idempotent n={n}"
            cnt += 1
        for a in range(-n, 2 * n + 1):
            if rho(Q(a, n)) != Q(a, n):
                return False, f"tick n={n}"
            for j in range(-7, 8):
                if rho(Q(a, n) + Q(j, 16 * n)) != Q(a, n):
                    return False, f"tolerance n={n}"
    return True, f"rho o rho = rho on {cnt} readings; ticks fixed; tolerance 1/(2n) for n<=64"


def t24():
    for x in range(-50, 51):
        for t in range(1, 65):
            if x + t == x or len({x + i for i in range(t)}) != t:
                return False, f"integers x={x} t={t}"
    for n in range(1, 65):
        for x in range(n):
            if (x + n) % n != x or len({(x + i) % n for i in range(n)}) != n:
                return False, f"Z/{n}"
            if any((x + t) % n == x for t in range(1, n)):
                return False, f"early return Z/{n}"
    return True, "no periodic point on Z (t<=64); first return exactly n on Z/n for n<=64"


# ---------------------------------------------------------------- section 8
def c1():
    cnt = 0
    for m in range(1, 65):
        for a, b in product(range(m), repeat=2):
            c, d = b, (a + b) % m
            if ((d - c) % m, c) != (a, b):
                return False, f"inverse m={m}"
            cnt += 1
        F = [0, 1]
        while len(F) < 202:
            F.append(F[-1] + F[-2])
        st = (0, 1 % m)
        for n in range(201):
            if st != (F[n] % m, F[n + 1] % m):
                return False, f"iterate m={m} n={n}"
            st = (st[1], (st[0] + st[1]) % m)
    return True, f"bijection on {cnt} pairs for m<=64; n-th iterate = (F_n, F_n+1) mod m, n<=200"


def c3():
    for k in range(10001):
        if (2 * k + 1) ** 2 % 4 != 1:
            return False, f"k={k}"
    for n in range(2001):
        for k in range(101):
            if 4 * n == (2 * k + 1) ** 2:
                return False, f"n={n} k={k}"
    for k in range(400):
        if (Q(2 * k + 1, 2) ** 2).denominator == 1:
            return False, f"half root k={k}"
    return True, "(2k+1)^2 = 1 mod 4 for k<=10000; no 4n=(2k+1)^2 for n<=2000, k<=100"


def c5():
    cnt = 0
    for w in range(1, 9):
        for a in range(2 ** w):
            for b in range(2 ** w):
                for cin in (0, 1):
                    s = a + b + cin
                    for i in range(w + 1):
                        win = []
                        for j in range(i - 1, -1, -1):
                            ai, bi = a >> j & 1, b >> j & 1
                            win += [("or", ai & bi), ("and", ai ^ bi)]
                        c = direct_F(win, cin)
                        if c != ((a % 2 ** i) + (b % 2 ** i) + cin) >> i:
                            return False, f"carry w={w} a={a} b={b} i={i}"
                        if i < w:
                            ai, bi = a >> i & 1, b >> i & 1
                            if ai ^ bi ^ c != s >> i & 1:
                                return False, f"sum bit w={w}"
                            g, p = ai & bi, ai ^ bi
                            if (g | p) + g != ai + bi:
                                return False, "position trit"
                    cnt += 1
    return True, f"carries and sum bits for {cnt} additions, widths 1..8, carry-in 0 and 1; position trit = a_i + b_i"


def main():
    run("T3", t3)
    run("T5", t5)
    run("T6", t6)
    run("T7", t7)
    run("T8", t8)
    run("T9", t9)
    run("T10", t10)
    run("T11", t11)
    run("T12", t12)
    run("T13", t13)
    run("T14", t14)
    run("T15", t15)
    run("T16", t16)
    try:
        hil = t17_19()
    except Exception as exc:
        hil = {k: (False, f"exception {exc}") for k in ("T17", "T18", "T19")}
    for sid in ("T17", "T18", "T19"):
        report(sid, *hil[sid])
    run("T21", t21)
    run("T23", t23)
    run("T24", t24)
    run("C1", c1)
    run("C3", c3)
    run("C5", c5)
    passed = all(r["pass"] for r in RESULTS)
    out = Path(__file__).resolve().parent / "evidence"
    out.mkdir(exist_ok=True)
    (out / "verification.json").write_text(json.dumps(
        {"complete": passed, "checks": RESULTS,
         "scope": "Finite checks of the stated ranges; the general statements are proved in paper.tex."},
        indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    print("all checks passed" if passed else "FAILURES: " + ", ".join(r["id"] for r in RESULTS if not r["pass"]))
    sys.exit(0 if passed else 1)


if __name__ == "__main__":
    main()
