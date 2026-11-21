#!/usr/bin/env python3
"""Independent finite checks for Winding and Mirrored.
Standard library only; exact integer and rational arithmetic throughout.
The Hilbert map is written here from Definition 6.1 of the Unifier paper,
twice: bottom-up by quarters and top-down point by point.
Gaussian rationals are pairs of Fractions; Python's complex type is not used.
Author: lmtlssss🜐. License: MIT.
"""
import json
import random
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


# ------------------------------------------------------------ Hilbert map
def sigma(q, x, y, s, untransposed=False):
    """The four maps of Definition 6.1 of the Unifier paper."""
    if q == 0:
        return (x, y) if untransposed else (y, x)
    if q == 1:
        return (x, y + s)
    if q == 2:
        return (x + s, y + s)
    return (2 * s - 1 - y, s - 1 - x)


def hilbert_table(k, untransposed=False):
    """H_k as a list, built bottom-up: H_{j+1}(q 4^j + r) = sigma_q(H_j(r))."""
    table = [(0, 0)]
    for j in range(k):
        s = 2 ** j
        table = [sigma(q, x, y, s, untransposed) for q in range(4) for (x, y) in table]
    return table


def hilbert_point(k, d):
    """H_k(d) evaluated top-down, independently of hilbert_table."""
    if k == 0:
        return (0, 0)
    q, r = divmod(d, 4 ** (k - 1))
    x, y = hilbert_point(k - 1, r)
    return sigma(q, x, y, 2 ** (k - 1))


def mirror(k, p):
    return (2 * 2 ** k - 1 - p[0], p[1])


def ring(H, k, forward_second_sheet=False):
    """C(j) = H(j) for j < N, C(j) = mu(H(2N-1-j)) for N <= j < 2N."""
    N = 4 ** k
    first = list(H)
    if forward_second_sheet:
        second = [mirror(k, H[j - N]) for j in range(N, 2 * N)]
    else:
        second = [mirror(k, H[2 * N - 1 - j]) for j in range(N, 2 * N)]
    return first + second


def neighbours(k, p, r):
    """Agree in one coordinate, differ by 1 in the other; x cyclic mod 2n."""
    m = 2 * 2 ** k
    if p[0] == r[0] and abs(p[1] - r[1]) == 1:
        return True
    return p[1] == r[1] and ((p[0] + 1) % m == r[0] or (r[0] + 1) % m == p[0])


def is_closed_unit_cycle(k, C):
    L = len(C)
    return all(neighbours(k, C[j], C[(j + 1) % L]) for j in range(L))


def cyc_dx(m, a, b):
    if (a + 1) % m == b:
        return 1
    if (b + 1) % m == a:
        return -1
    return 0


KMAX = 8
CACHE = {}


def data(k):
    if k not in CACHE:
        H = hilbert_table(k)
        CACHE[k] = (H, ring(H, k))
    return CACHE[k]


def w1():
    cells = 0
    for k in range(KMAX + 1):
        n, N = 2 ** k, 4 ** k
        H, C = data(k)
        for d in range(N):
            if H[d] != hilbert_point(k, d):
                return False, f"bottom-up and top-down Hilbert maps differ at k={k}, d={d}"
        if sorted(H) != [(x, y) for x in range(n) for y in range(n)]:
            return False, f"H_{k} is not a bijection onto the grid"
        R = [(x, y) for x in range(2 * n) for y in range(n)]
        if len(C) != 2 * N or sorted(C) != R:
            return False, f"C_{k} is not a bijection onto R"
        cells += 2 * N
    return True, (f"C is a bijection onto R for k=0..{KMAX} ({cells} cells in all; "
                  f"{2 * 4 ** KMAX} at k={KMAX}); bottom-up H equals top-down H")


def w2():
    checks = 0
    for k in range(KMAX + 1):
        n, N = 2 ** k, 4 ** k
        _, C = data(k)
        for x in range(2 * n):
            for y in range(n):
                if mirror(k, mirror(k, (x, y))) != (x, y):
                    return False, f"mu is not an involution at k={k}"
        for j in range(2 * N):
            if C[2 * N - 1 - j] != mirror(k, C[j]):
                return False, f"C(2N-1-j) != mu(C(j)) at k={k}, j={j}"
            checks += 1
    return True, f"mu(mu(p)) = p on R and C(2N-1-j) = mu(C(j)) for all {checks} indices, k=0..{KMAX}"


def w3():
    steps = 0
    for k in range(KMAX + 1):
        n, N = 2 ** k, 4 ** k
        _, C = data(k)
        if not is_closed_unit_cycle(k, C):
            return False, f"a step of C_{k} is not a unit step"
        if (C[N - 1], C[N], C[2 * N - 1], C[0]) != ((n - 1, 0), (n, 0), (2 * n - 1, 0), (0, 0)):
            return False, f"join or closure wrong at k={k}"
        steps += 2 * N
    # Mutations: each must be detected.
    caught = []
    for k in range(1, KMAX + 1):
        H = hilbert_table(k)
        if is_closed_unit_cycle(k, ring(H, k, forward_second_sheet=True)):
            return False, f"mutation not detected: second sheet traversed forward, k={k}"
    caught.append("second sheet forward")
    for k in range(2, KMAX + 1):
        Hm = hilbert_table(k, untransposed=True)
        if is_closed_unit_cycle(k, ring(Hm, k)):
            return False, f"mutation not detected: first quarter untransposed, k={k}"
    caught.append("first Hilbert quarter untransposed")
    return True, (f"all {steps} steps unit steps of the periodic rectangle, k=0..{KMAX}; "
                  f"join (n-1,0)->(n,0), closure (2n-1,0)->(0,0); mutations caught: {', '.join(caught)}")


def w4():
    for k in range(1, KMAX + 1):
        n, N = 2 ** k, 4 ** k
        m = 2 * n
        _, C = data(k)
        L = 2 * N
        sx = sum(cyc_dx(m, C[j][0], C[(j + 1) % L][0]) for j in range(L))
        sy = sum(C[(j + 1) % L][1] - C[j][1] for j in range(L))
        rev = [C[L - 1 - j] for j in range(L)]
        rx = sum(cyc_dx(m, rev[j][0], rev[(j + 1) % L][0]) for j in range(L))
        ry = sum(rev[(j + 1) % L][1] - rev[j][1] for j in range(L))
        if (sx, sy, rx, ry) != (m, 0, -m, 0):
            return False, f"k={k}: sums {(sx, sy, rx, ry)}"
        if [mirror(k, p) for p in C] != rev:
            return False, f"k={k}: mirror image is not the reversed ring"
        plain = sum(C[(j + 1) % L][0] - C[j][0] for j in range(L))
        if plain == m:
            return False, "mutation not detected: plain x differences"
    # At k = 0 the two columns make +1 and -1 the same cyclic step.
    ambiguous = (0 + 1) % 2 == 1 and (1 + 1) % 2 == 0
    if not ambiguous:
        return False, "k=0 ambiguity not reproduced"
    return True, (f"sum dx = 2n, sum dy = 0, winding (1,0); reversed ring (-1,0); for k=1..{KMAX}; "
                  f"mu(C) is the reversed ring; plain x differences sum to 0 (mutation caught); "
                  f"sign undefined at k=0")


# ------------------------------------------------------------ W5
def mean(F, cells):
    sx = sum(F[p][0] for p in cells)
    sy = sum(F[p][1] for p in cells)
    return (sx / len(cells), sy / len(cells))


def vec_mirror(k, F):
    return {p: (-F[mirror(k, p)][0], F[mirror(k, p)][1]) for p in F}


def w5():
    rng = random.Random(20261121)
    fields = 0
    for k in range(0, 4):
        n = 2 ** k
        cells = [(x, y) for x in range(2 * n) for y in range(n)]
        for trial in range(6):
            if trial < 3:  # the source's weighted field F = (o/5) t with o = 7
                F = {p: (Q(7, 5) * rng.randint(-9, 9), Q(7, 5) * rng.randint(-9, 9)) for p in cells}
            else:
                F = {p: (Q(rng.randint(-50, 50), rng.randint(1, 13)),
                         Q(rng.randint(-50, 50), rng.randint(1, 13))) for p in cells}
            h = mean(F, cells)
            G = {p: (F[p][0] - h[0], F[p][1] - h[1]) for p in cells}
            MG = vec_mirror(k, G)
            if vec_mirror(k, MG) != G or vec_mirror(k, vec_mirror(k, F)) != F:
                return False, "M is not an involution"
            if mean(MG, cells) != (0, 0) or mean(G, cells) != (0, 0):
                return False, "M does not preserve mean zero"
            tor = {p: ((G[p][0] - MG[p][0]) / 2, (G[p][1] - MG[p][1]) / 2) for p in cells}
            drv = {p: ((G[p][0] + MG[p][0]) / 2, (G[p][1] + MG[p][1]) / 2) for p in cells}
            for p in cells:
                if (tor[p][0] + drv[p][0] + h[0], tor[p][1] + drv[p][1] + h[1]) != F[p]:
                    return False, "F != m + k + h"
            Mt, Md = vec_mirror(k, tor), vec_mirror(k, drv)
            if any(Mt[p] != (-tor[p][0], -tor[p][1]) for p in cells):
                return False, "M m != -m"
            if Md != drv:
                return False, "M k != k"
            if mean(tor, cells) != (0, 0) or mean(drv, cells) != (0, 0):
                return False, "m or k has nonzero mean"
            fields += 1
    return True, (f"F = m + k + h, Mm = -m, Mk = k, mean m = mean k = 0 on {fields} rational fields, "
                  f"rectangles 2x1 to 16x8, including F = (7/5) t")


# ------------------------------------------------------------ W6
def divergence(ex, ey, mx, my):
    return {(x, y): ex[(x, y)] + ey[(x, y)] - ex[((x - 1) % mx, y)] - ey[(x, (y - 1) % my)]
            for x in range(mx) for y in range(my)}


def w6():
    rng = random.Random(6)
    cases = 0
    for n in range(1, 33):
        mx, my = 2 * n, n
        cells = [(x, y) for x in range(mx) for y in range(my)]
        for _ in range(3):
            ex = {p: Q(rng.randint(-20, 20), rng.randint(1, 9)) for p in cells}
            ey = {p: Q(rng.randint(-20, 20), rng.randint(1, 9)) for p in cells}
            if sum(divergence(ex, ey, mx, my).values()) != 0:
                return False, f"(a) fails at {mx}x{my}"
        for c in (Q(0), Q(3, 2), Q(-2)):
            for q in (Q(7), Q(-1, 3), Q(0)):
                sl, sr = (n - 1, 0), (n, 0)
                ex = {p: c + (q if p == sl else 0) for p in cells}
                ey = {p: Q(0) for p in cells}
                div = divergence(ex, ey, mx, my)
                for p in cells:
                    want = q if p == sl else (-q if p == sr else 0)
                    if div[p] != want:
                        return False, f"(b) divergence at {p}, size {mx}x{my}"
                left = sum(div[p] for p in cells if p[0] < n)
                right = sum(div[p] for p in cells if p[0] >= n)
                if (left, right) != (q, -q):
                    return False, f"(b) sheet sums at {mx}x{my}"
                cases += 1
    return True, (f"(a) on 96 random rational edge fields; (b) {cases} seam fields "
                  f"(c in {{0, 3/2, -2}}, q in {{7, -1/3, 0}}); every grid 2n x n, n = 1..32")


# ------------------------------------------------------------ W7
def w7():
    ns = [Q(v) for v in (-3, -1, 0, 1, 3)] + [Q(1, 2), Q(-7, 3)]
    us = [Q(i, 20) for i in range(-20, 21)]
    for n in ns:
        aN = lambda u: n * (1 - u) / 2
        aS = lambda u: -n * (1 + u) / 2
        for u in us:
            if aN(u) - aS(u) != n:
                return False, f"(a) n={n} u={u}"
        if aN(Q(1)) != 0 or aS(Q(-1)) != 0:
            return False, f"(b) n={n}"
        for u, v in zip(us, us[1:]):
            if (aN(v) - aN(u)) / (v - u) != -n / 2 or (aS(v) - aS(u)) / (v - u) != -n / 2:
                return False, f"(c) n={n}"
        riemann = sum((v - u) * (n / 2) for u, v in zip(us, us[1:]))
        if riemann != n:
            return False, f"(d) n={n}"
    return True, (f"overlap n, regular poles, both slopes -n/2 on 41 rational u in [-1,1]; "
                  f"flux n; n in {{-3,-1,0,1,3,1/2,-7/3}}")


# ------------------------------------------------------------ W8
def w8():
    r = tuple((x + 1) % 12 for x in range(12))
    s = tuple((-x) % 12 for x in range(12))
    e = tuple(range(12))

    def comp(f, g):  # f after g
        return tuple(f[g[x]] for x in range(12))

    def power(f, a):
        out = e
        for _ in range(a):
            out = comp(f, out)
        return out

    def order(f):
        a, g = 1, f
        while g != e:
            g, a = comp(f, g), a + 1
        return a

    rinv = tuple(r.index(x) for x in range(12))
    if order(r) != 12 or order(s) != 2:
        return False, "orders"
    if comp(s, comp(r, s)) != rinv:
        return False, "s r s != r^-1"
    maps = {comp(power(r, a), power(s, b)) for a in range(12) for b in range(2)}
    if len(maps) != 24:
        return False, f"{len(maps)} distinct maps"
    if any(comp(f, g) not in maps for f in maps for g in maps):
        return False, "not closed"
    return True, "r of order 12, s of order 2, s r s = r^-1; 24 distinct maps r^a s^b, closed under composition"


# ------------------------------------------------------------ W9
def odd_primes(limit):
    sieve = [True] * limit
    sieve[0:2] = [False, False]
    for i in range(2, limit):
        if sieve[i]:
            for j in range(i * i, limit, i):
                sieve[j] = False
    return [p for p in range(3, limit) if sieve[p]]


def w9():
    primes = odd_primes(200)
    pairs = 0
    for p in primes:
        inv = {b: pow(b, p - 2, p) for b in range(1, p)}
        D = [(a, b) for a in range(p) for b in range(1, p)]
        div = {(a, b): a * inv[b] % p for (a, b) in D}
        for (a, b) in D:
            v = div[(a, b)]
            if div[((-a) % p, b)] != (-v) % p or div[(a, (-b) % p)] != (-v) % p \
                    or div[((-a) % p, (-b) % p)] != v:
                return False, f"(a) p={p} at {(a, b)}"
        seen, sizes = set(), []
        for x in D:
            if x in seen:
                continue
            a, b = x
            orbit = {(sa * a % p, sb * b % p) for sa in (1, -1) for sb in (1, -1)}
            if any(y[1] == 0 for y in orbit):
                return False, f"orbit leaves D at p={p}"
            seen |= orbit
            sizes.append(len(orbit))
        h = (p - 1) // 2
        want = ((p - 1) ** 2 // 4, (p - 1) // 2, (p * p - 1) // 4)
        got = (sizes.count(4), sizes.count(2), len(sizes))
        if len(D) != p * (p - 1) or got != want or len(sizes) != got[0] + got[1]:
            return False, f"(b) p={p}: {got} != {want}"
        reps = [(a, b) for a in range(h + 1) for b in range(1, h + 1)]
        hit = {}
        for (a, b) in reps:
            key = frozenset((sa * a % p, sb * b % p) for sa in (1, -1) for sb in (1, -1))
            hit[key] = hit.get(key, 0) + 1
        if len(reps) != (h + 1) * h or len(hit) != len(sizes) or set(hit.values()) != {1}:
            return False, f"(b) representatives p={p}"
        if p == 97:
            table = {}
            for (a, b) in reps:
                v = div[(a, b)]
                table[(a, b)], table[((-a) % p, b)] = v, (-v) % p
                table[(a, (-b) % p)], table[((-a) % p, (-b) % p)] = (-v) % p, v
            if (len(D), len(sizes), got[0], got[1]) != (9312, 2352, 2304, 48) or table != div:
                return False, "(c) p=97"
        pairs += len(D)
    return True, (f"orbit counts by enumeration for all {len(primes)} odd primes below 200 "
                  f"({pairs} pairs); p=97: 9312 pairs, 2352 orbits (2304 of size 4, 48 of size 2), "
                  f"all 9312 quotients rebuilt from the 2352 representatives")


# ------------------------------------------------------------ W10
def complete4():
    return 4, [(a, b) for a in range(4) for b in range(a + 1, 4)]


def prism():
    tri = [(0, 1), (1, 2), (2, 0), (3, 4), (4, 5), (5, 3)]
    return 6, tri + [(0, 3), (1, 4), (2, 5)]


def honeycomb_patch():
    """Three hexagons around vertex 0: 13 vertices, 15 edges; 0, 1, 2, 3 have degree 3."""
    a, b, c, d, e, f, g, h, i = range(4, 13)
    edges = [(0, 1), (0, 2), (0, 3),
             (1, a), (a, b), (b, c), (c, 2),
             (2, d), (d, e), (e, f), (f, 3),
             (3, g), (g, h), (h, i), (i, 1)]
    return 13, edges


def honeycomb_torus():
    """Honeycomb on the 2 x 2 torus: 8 vertices of degree 3, 12 edges."""
    L = 2
    A = lambda i, j: 2 * ((i % L) * L + (j % L))
    B = lambda i, j: A(i, j) + 1
    edges = []
    for i in range(L):
        for j in range(L):
            edges += [(A(i, j), B(i, j)), (A(i, j), B(i + 1, j)), (A(i, j), B(i, j + 1))]
    return 2 * L * L, edges


def w10():
    total = 0
    names = []
    for name, (nv, edges) in (("K4", complete4()), ("prism", prism()),
                              ("honeycomb patch", honeycomb_patch()),
                              ("honeycomb 2x2 torus", honeycomb_torus())):
        if any(u == v for u, v in edges):
            return False, f"loop in {name}"
        deg = [sum((u == v) + (w == v) for u, w in edges) for v in range(nv)]
        E = len(edges)
        tally = {v: {} for v in range(nv) if deg[v] == 3}
        for o in product((0, 1), repeat=E):
            q = [0] * nv
            for (u, w), bit in zip(edges, o):
                head, tail = (w, u) if bit == 0 else (u, w)
                q[head] += 1
                q[tail] -= 1
            if sum(q) != 0:
                return False, f"(b) {name}"
            for v in range(nv):
                if (q[v] - deg[v]) % 2 != 0 or (deg[v] % 2 == 1 and q[v] == 0):
                    return False, f"(a) {name} vertex {v}"
                if deg[v] == 3:
                    tally[v][q[v]] = tally[v].get(q[v], 0) + 1
        scale = 2 ** (E - 3)
        for v, t in tally.items():
            if t != {3: scale, 1: 3 * scale, -1: 3 * scale, -3: scale}:
                return False, f"(c) {name} vertex {v}: {t}"
        total += 2 ** E
        names.append(f"{name} ({nv} vertices, {E} edges)")
    return True, (f"parity, nonzero odd corners, zero total and the 1:3:3:1 split at degree-3 corners "
                  f"on all {total} orientations of " + ", ".join(names))


# ------------------------------------------------------------ W11
class G:
    """Gaussian rational x + y i with Fraction parts."""
    __slots__ = ("x", "y")

    def __init__(self, x, y=0):
        self.x, self.y = Q(x), Q(y)

    def __add__(self, o):
        return G(self.x + o.x, self.y + o.y)

    def __sub__(self, o):
        return G(self.x - o.x, self.y - o.y)

    def __neg__(self):
        return G(-self.x, -self.y)

    def __mul__(self, o):
        return G(self.x * o.x - self.y * o.y, self.x * o.y + self.y * o.x)

    def norm2(self):
        return self.x * self.x + self.y * self.y

    def inv(self):
        n = self.norm2()
        if n == 0:
            raise ZeroDivisionError("Gaussian rational zero")
        return G(self.x / n, -self.y / n)

    def __truediv__(self, o):
        return self * o.inv()

    def __eq__(self, o):
        return self.x == o.x and self.y == o.y

    def __hash__(self):
        return hash((self.x, self.y))


ONE, ZERO = G(1), G(0)


def mobius(w):
    return (ONE + w) / (ONE - w)


def zeta(u):
    """z = (u - 1)/(u + 1): the value of tanh(ct/2) when u = exp(ct)."""
    return (u - ONE) / (u + ONE)


def w11():
    us = []
    for den in (1, 2, 3, 5):
        for a in range(-6, 7):
            for b in range(-6, 7):
                u = G(Q(a, den), Q(b, den))
                if u.norm2() != 0 and not (u == -ONE):
                    us.append(u)
    us = list(dict.fromkeys(us))
    for u in us:
        z = zeta(u)
        if ONE - z == ZERO:
            return False, "(b) 1 - z = 0"
        if mobius(z) != u:
            return False, "(b) (1+z)/(1-z) != u"
        if zeta(u.inv()) != -z:
            return False, "(a) u -> 1/u does not give z -> -z"
        if mobius(z).norm2() != u.norm2():
            return False, "(c)"
        if (z - ONE).norm2() * (u + ONE).norm2() != 4:
            return False, "(e) |z-1|^2 |u+1|^2 != 4"
        if (zeta(u.inv()) + ONE).norm2() != (z - ONE).norm2():
            return False, "(e) mirror"
    # (e), the bound, at points u = exp(ct) whose modulus |u| = exp(at) is rational:
    # |z - 1| <= 2/(|u| - 1) for |u| > 1 and |z + 1| <= 2/(1/|u| - 1) for |u| < 1.
    bounded = 0
    units = [G(1), G(-1), G(0, 1), G(0, -1)] + [G(Q(x, 5), Q(y, 5)) for x, y in
                                                  ((3, 4), (3, -4), (-3, 4), (-3, -4), (4, 3), (4, -3), (-4, 3), (-4, -3))]
    radii = [Q(8, 7), Q(6, 5), Q(3, 2), Q(2), Q(3), Q(7, 2), Q(10), Q(100)]
    for w in units:
        for r in radii:
            u = G(r) * w
            if u == -ONE:
                continue
            if (zeta(u) - ONE).norm2() * (r - 1) ** 2 > 4:
                return False, f"(e) bound at |u| = {r}"
            v = u.inv()
            if (zeta(v) + ONE).norm2() * (r - 1) ** 2 > 4:
                return False, f"(e) mirror bound at |u| = 1/{r}"
            bounded += 2
    if zeta(ONE) != ZERO or mobius(-ONE) != ZERO:
        return False, "(a)/(b) fixed values"
    sample = us[::7]
    products = 0
    for u1 in sample:
        for u2 in sample:
            if u1 * u2 == -ONE:  # u = exp(ct) is never -1 when a != 0
                continue
            products += 1
            if mobius(zeta(u1 * u2)).norm2() != u1.norm2() * mobius(zeta(u2)).norm2():
                return False, "(d)"
    return True, (f"(1+z)/(1-z) = u, 1-z != 0, z(1/u) = -z(u), squared ratios (c) and (d), "
                  f"|z-1|^2 |u+1|^2 = 4, on {len(us)} Gaussian rationals u and {products} products; "
                  f"the bounds of (e) at {bounded} points of rational modulus; "
                  f"the exponential law and the limits are not checked here")


def main():
    for sid, fn in (("W1", w1), ("W2", w2), ("W3", w3), ("W4", w4), ("W5", w5), ("W6", w6),
                    ("W7", w7), ("W8", w8), ("W9", w9), ("W10", w10), ("W11", w11)):
        run(sid, fn)
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
