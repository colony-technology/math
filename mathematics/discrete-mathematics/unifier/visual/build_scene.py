#!/usr/bin/env python3
"""The Unifier, cover figure. Native Blender scene in the graphite/cyan visual system.

Built from exact rational geometry, the way the three-bit figure is built from its trace.

The floor (the plane z = 0) carries the straight picture: parallel lines v = Y_j and one
row of equal circles of radius 1/2, centred on the line v = 8/5, between v = 11/10 and v = 21/10.
Inversion in the touching point N = (0, 0, 1) with radius sqrt(2) carries the floor onto the
unit sphere (the stereographic lift) and the picture onto the dome: circles that touch at N,
and a chain of tangent circles that shrinks toward N from both sides. Seen from N the dome
picture is the floor picture again. The point at infinity of the floor is N.

Every fact the image draws is asserted in exact rational arithmetic before anything renders,
and the facts are written to evidence.json beside this file. Nothing typed appears in the image.

Run:  blender -b -P build_scene.py -- [WIDTH HEIGHT OUTPUT.png [key=value ...]]
      defaults: 3840 2160 00-cover-4k.png
      keys (tests only; the defaults are the published figure):
        border=x0,x1,y0,y1  save=0|1  samples=64  elev=23  ortho=5.6  vc=-0.25
        rays=1  ground=.00399,.0065,.0098
Author: lmtlssss🜐.
"""
import hashlib, json, math, sys, time
from fractions import Fraction as F
from pathlib import Path

ROOT = Path(__file__).resolve().parent
ARGV = sys.argv[sys.argv.index('--') + 1:] if '--' in sys.argv else []
WIDTH = int(ARGV[0]) if len(ARGV) > 0 else 3840
HEIGHT = int(ARGV[1]) if len(ARGV) > 1 else 2160
OUTPUT = ROOT / (ARGV[2] if len(ARGV) > 2 else '00-cover-4k.png')
OPT = dict(a.split('=', 1) for a in ARGV[3:])

# ---------------------------------------------------------------------------------------------
# 1. Exact geometry (no Blender needed)
# ---------------------------------------------------------------------------------------------
def dot(a, b):
    return sum(x * y for x, y in zip(a, b))

N = (F(0), F(0), F(1))          # the touching point: top of the unit sphere
K2 = F(2)                       # squared radius of the inversion centred at N

def invert(p):
    """Inversion in the sphere of centre N and squared radius 2 (any point other than N)."""
    d = tuple(pi - ni for pi, ni in zip(p, N))
    s = dot(d, d)
    assert s != 0
    return tuple(ni + K2 * di / s for ni, di in zip(N, d))

def lift(q):
    """Floor point (u, v) -> its inversion image on the unit sphere."""
    return invert((q[0], q[1], F(0)))

def drop(P):
    """Sphere point other than N -> its inversion image on the floor."""
    Q = invert(P)
    assert Q[2] == 0
    return (Q[0], Q[1])

# Circles on the unit sphere are planes n.P = d.
def lift_circle(a, b, r2):
    """Floor circle (centre (a, b), squared radius r2) -> plane of its image on the sphere."""
    c = a * a + b * b - r2
    return ((2 * a, 2 * b, c - 1), 1 + c)

def lift_line(alpha, beta, gamma):
    """Floor line alpha*u + beta*v = gamma -> plane of its image (a circle through N)."""
    return ((alpha, beta, gamma), gamma)

def drop_circle(plane):
    """Plane of a sphere circle -> ('line', (n1, n2, d)) if it passes through N, else ('circle', (a, b, r2))."""
    n, d = plane
    if n[2] == d:
        return ('line', (n[0], n[1], d))
    a, b = n[0] / (d - n[2]), n[1] / (d - n[2])
    c = (d + n[2]) / (d - n[2])
    return ('circle', (a, b, a * a + b * b - c))

def sphere_contact(p1, p2):
    """Common line of two circle planes; returns (squared distance of that line from the centre, nearest point).
    The two circles on the unit sphere are tangent exactly when that squared distance is 1."""
    (n1, d1), (n2, d2) = p1, p2
    a, b, c = dot(n1, n1), dot(n1, n2), dot(n2, n2)
    G = a * c - b * b
    assert G != 0, 'parallel planes'
    al, be = (d1 * c - d2 * b) / G, (d2 * a - d1 * b) / G
    p = tuple(al * x + be * y for x, y in zip(n1, n2))
    assert dot(n1, p) == d1 and dot(n2, p) == d2
    return dot(p, p), p

def floor_circle_points(a, b, r, ts):
    """Rational points of a floor circle with rational radius, by the rational parametrisation."""
    return [(a + r * (1 - t * t) / (1 + t * t), b + r * 2 * t / (1 + t * t)) for t in ts]

# The straight picture on the floor.
RHO = F(1, 2)                       # radius of the equal circles
YC = F(8, 5)                        # the row lies on the line v = 8/5
OUTER, INNER = YC - RHO, YC + RHO   # its strip: 11/10 <= v <= 21/10, outside the unit disk
DELTA = F(1)                        # spacing of the parallel lines: every strip as wide as the row
M = 14                              # row circles n = -M .. M, centres (n, 8/5)
J = 7                               # parallel lines v = 21/10 + j, j = 0 .. J
ROW = [(F(n) * 2 * RHO, YC) for n in range(-M, M + 1)]
LINES = [INNER + j * DELTA for j in range(J + 1)]
CONTACTS = [((ROW[i][0] + ROW[i + 1][0]) / 2, YC) for i in range(len(ROW) - 1)]

facts = []
def fact(fid, statement, cases):
    facts.append({'id': fid, 'statement': statement, 'cases_checked': cases, 'result': True})
    print('ASSERTED', fid, '-', statement, '(%d cases)' % cases, flush=True)

assert OUTER > 1, 'the strip must lie outside the unit disk so that the chain lies on the dome'

# The inversion: floor <-> sphere, and it is its own inverse.
samples = list(CONTACTS) + [(F(p), F(q, 3)) for p in range(-6, 7) for q in range(-9, 10)]
for q in samples:
    P = lift(q)
    assert dot(P, P) == 1
    assert drop(P) == q
    assert invert(P) == (q[0], q[1], F(0))
fact('I1', 'inversion in N with radius sqrt 2 sends each sampled floor point onto the unit sphere, '
     'and back to itself', len(samples))

for (a, b, r2), ts in [((F(n), YC, RHO * RHO), [F(t, 7) for t in range(-14, 15)]) for n in range(-M, M + 1)]:
    plane = lift_circle(a, b, r2)
    for q in floor_circle_points(a, b, RHO, ts):
        assert dot(plane[0], lift(q)) == plane[1]
fact('I2', 'the lift of each row circle lies in the plane computed for it (29 rational points per circle)',
     (2 * M + 1) * 29)

# Before the inversion is undone: the dome picture.
CHAIN = [lift_circle(a, b, RHO * RHO) for a, b in ROW]
NESTED = [lift_line(F(0), F(1), y) for y in LINES]
BOUND_OUT = lift_line(F(0), F(1), OUTER)
BOUND_IN = NESTED[0]

for pl in NESTED + [BOUND_OUT]:
    assert dot(pl[0], N) == pl[1]
fact('B1', 'every nested circle on the dome passes through N', len(NESTED) + 1)

fam = NESTED + [BOUND_OUT]
pairs = 0
for i in range(len(fam)):
    for j in range(i + 1, len(fam)):
        d2, p = sphere_contact(fam[i], fam[j])
        assert d2 == 1 and p == N
        pairs += 1
fact('B2', 'every two nested circles touch, and they touch at N', pairs)

for i in range(len(CHAIN) - 1):
    d2, p = sphere_contact(CHAIN[i], CHAIN[i + 1])
    assert d2 == 1 and p == lift(CONTACTS[i])
fact('B3', 'consecutive circles of the chain touch, at the lift of the floor contact point', len(CHAIN) - 1)

for pl in CHAIN:
    for bd in (BOUND_OUT, BOUND_IN):
        d2, p = sphere_contact(pl, bd)
        assert d2 == 1
    assert dot(pl[0], N) != pl[1]
fact('B4', 'every chain circle touches both boundary circles of its crescent and misses N', 2 * len(CHAIN))

disj = 0
for i in range(len(CHAIN)):
    for j in range(i + 2, len(CHAIN)):
        d2, p = sphere_contact(CHAIN[i], CHAIN[j])
        assert d2 > 1
        disj += 1
fact('B5', 'chain circles that are not neighbours are disjoint', disj)

def sphere_r2(pl):
    n, d = pl
    return 1 - d * d / dot(n, n)

for k in range(1, M + 1):
    assert sphere_r2(CHAIN[M + k]) == sphere_r2(CHAIN[M - k])
    assert sphere_r2(CHAIN[M + k]) < sphere_r2(CHAIN[M + k - 1])
for i in range(len(NESTED) - 1):
    assert sphere_r2(NESTED[i + 1]) < sphere_r2(NESTED[i])
fact('B6', 'the chain is symmetric and its circles shrink strictly toward N; the nested circles shrink toward N',
     M + len(NESTED) - 1)

# After the inversion is undone: the straight picture again.
dropped_nested = [drop_circle(pl) for pl in NESTED]
for kind, (n1, n2, d) in dropped_nested:
    assert kind == 'line' and n1 == 0 and n2 != 0
offsets = [d / n2 for _, (n1, n2, d) in dropped_nested]
assert all(offsets[i + 1] - offsets[i] == DELTA for i in range(len(offsets) - 1))
fact('A1', 'the nested circles become straight lines, all parallel (normal (0,1)), equally spaced by 1',
     len(NESTED))

dropped_chain = [drop_circle(pl) for pl in CHAIN]
for kind, _ in dropped_chain:
    assert kind == 'circle'
centres = [(a, b) for _, (a, b, r2) in dropped_chain]
radii2 = {r2 for _, (a, b, r2) in dropped_chain}
assert radii2 == {RHO * RHO}
for i in range(len(centres) - 2):
    (x0, y0), (x1, y1), (x2, y2) = centres[i:i + 3]
    assert (x1 - x0) * (y2 - y0) - (y1 - y0) * (x2 - x0) == 0
for i in range(len(centres) - 1):
    (x0, y0), (x1, y1) = centres[i], centres[i + 1]
    assert (x1 - x0) ** 2 + (y1 - y0) ** 2 == (2 * RHO) ** 2
fact('A2', 'the chain becomes one straight row of equal circles: equal radii 1/2, collinear centres, '
     'neighbours at distance 1 = 2r', len(CHAIN))

kind_o, (o1, o2, od) = drop_circle(BOUND_OUT)
kind_i, (i1, i2, idd) = drop_circle(BOUND_IN)
assert kind_o == kind_i == 'line' and o1 == i1 == 0
for a, b in centres:
    assert abs(b - od / o2) == RHO and abs(b - idd / i2) == RHO
fact('A3', 'the two boundary circles become the lines v = 11/10 and v = 21/10, and each row circle touches both',
     2 * len(centres))

# Lines of sight from N: N, each contact point of the chain and its contact point of the row are collinear,
# and the dome point lies between N and the floor point.
for c in CONTACTS:
    P, Q = lift(c), (c[0], c[1], F(0))
    a = tuple(p - n for p, n in zip(P, N))
    b = tuple(q - n for q, n in zip(Q, N))
    cross = (a[1] * b[2] - a[2] * b[1], a[2] * b[0] - a[0] * b[2], a[0] * b[1] - a[1] * b[0])
    assert cross == (0, 0, 0)
    t = dot(a, b) / dot(b, b)
    assert 0 < t < 1
fact('R1', 'N, each contact point of the chain on the dome and the matching contact point of the row on the floor '
     'are collinear, the dome point between the other two', len(CONTACTS))

# ---------------------------------------------------------------------------------------------
# 2. Evidence
# ---------------------------------------------------------------------------------------------
def s(x):
    return str(x) if isinstance(x, F) else [s(y) for y in x]

exact = {
    'touching_point_N': s(N),
    'inversion': 'centre N, squared radius 2: P -> N + 2 (P - N) / |P - N|^2 ; floor z = 0 <-> unit sphere',
    'row_circles': {'radius': s(RHO), 'centres': [s(c) for c in ROW]},
    'strip': [s(OUTER), s(INNER)],
    'parallel_lines_v': [s(y) for y in LINES],
    'dome_chain_planes': [{'n': s(pl[0]), 'd': s(pl[1]), 'r2': s(sphere_r2(pl))} for pl in CHAIN],
    'dome_nested_planes': [{'n': s(pl[0]), 'd': s(pl[1]), 'r2': s(sphere_r2(pl))} for pl in [BOUND_OUT] + NESTED],
    'floor_contacts': [s(c) for c in CONTACTS],
    'dome_contacts': [s(lift(c)) for c in CONTACTS],
}
blob = json.dumps(exact, sort_keys=True, separators=(',', ':')).encode()
evidence = {
    'schema': 'mathematics.figure.evidence.v1',
    'figure': 'The Unifier, cover: the straight picture and its inversion in the touching point',
    'author': 'lmtlssss🜐',
    'generator': 'visual/build_scene.py (exact rational arithmetic, Python fractions)',
    'facts': facts,
    'exact_data_sha256': hashlib.sha256(blob).hexdigest(),
    'exact_data': exact,
}
(ROOT / 'evidence.json').write_text(json.dumps(evidence, indent=2, ensure_ascii=False) + '\n', encoding='utf-8')
print('EVIDENCE', ROOT / 'evidence.json', len(facts), 'facts', flush=True)

# ---------------------------------------------------------------------------------------------
# 3. Scene (only under Blender)
# ---------------------------------------------------------------------------------------------
try:
    import bpy
    from mathutils import Vector
except ImportError:
    sys.exit(0)

bpy.ops.wm.read_factory_settings(use_empty=True)
scene = bpy.context.scene
for engine in ('BLENDER_EEVEE', 'BLENDER_EEVEE_NEXT'):
    try:
        scene.render.engine = engine
        break
    except Exception:
        pass
scene.render.resolution_x = WIDTH
scene.render.resolution_y = HEIGHT
scene.render.resolution_percentage = 100
scene.render.image_settings.file_format = 'PNG'
scene.render.image_settings.color_mode = 'RGB'
scene.render.image_settings.color_depth = '8'
scene.render.filepath = str(OUTPUT)
scene.render.film_transparent = False
# No render metadata in the PNG (Blender's default stamp fields include the .blend path and the date).
for attr in dir(scene.render):
    if attr.startswith('use_stamp'):
        try:
            setattr(scene.render, attr, False)
        except Exception:
            pass
try:
    scene.eevee.taa_render_samples = int(OPT.get('samples', 64))
except Exception:
    pass
scene.view_settings.view_transform = 'Standard'
try:
    scene.view_settings.look = 'Medium High Contrast'
except Exception:
    pass
print('LOOK', scene.render.engine, scene.view_settings.view_transform, scene.view_settings.look, flush=True)
if 'border' in OPT:
    x0, x1, y0, y1 = map(float, OPT['border'].split(','))
    scene.render.use_border = True
    scene.render.use_crop_to_border = True
    scene.render.border_min_x, scene.render.border_max_x = x0, x1
    scene.render.border_min_y, scene.render.border_max_y = y0, y1

world = bpy.data.worlds.new('Graphite / #080d12')
scene.world = world
try:
    world.use_nodes = True
except Exception:
    pass
for node in world.node_tree.nodes:
    if node.type == 'BACKGROUND':
        node.inputs['Color'].default_value = (.0046, .0078, .0115, 1)
        node.inputs['Strength'].default_value = .5

def col(name):
    c = bpy.data.collections.new(name)
    scene.collection.children.link(c)
    return c

C_FLOOR = col('01 / floor: parallel lines and one straight row of equal circles')
C_DOME = col('02 / dome: the same picture after inversion in N')
C_POINT = col('03 / the touching point N, the point at infinity of the floor')
C_STAGE = col('04 / camera and graphite ground')

def emission(name, color, strength=1.0):
    mat = bpy.data.materials.new(name)
    mat.diffuse_color = tuple(color) + (1,)
    try:
        mat.use_nodes = True
    except Exception:
        pass
    nodes = mat.node_tree.nodes
    nodes.clear()
    em = nodes.new('ShaderNodeEmission')
    em.inputs['Color'].default_value = tuple(color) + (1,)
    em.inputs['Strength'].default_value = strength
    out = nodes.new('ShaderNodeOutputMaterial')
    mat.node_tree.links.new(em.outputs['Emission'], out.inputs['Surface'])
    return mat

# House colours, from the three-bit and analysis covers.
INK = emission('white / foreground', (.84, .90, .93), 1.15)
PALE = emission('soft white', (.54, .68, .73), .88)
DIM = emission('construction / graphite blue', (.17, .31, .38), .65)
GOLD = emission('touching point / gold', (.96, .75, .38), 1.3)
ROUTE = emission('row and chain / cyan', (.53, .79, .85), 1.0)
# Ground emission measured in Blender 5.2.3 (Standard, Medium High Contrast) to render as #080d12, the house graphite.
GROUND = emission('flat graphite field', tuple(float(x) for x in OPT.get('ground', '.00399,.0065,.0098').split(',')), 1.0)

# Camera: orthographic, from the front and above.
ELEV = math.radians(float(OPT.get('elev', 23)))
VIEW = Vector((0, math.cos(ELEV), math.sin(ELEV)))      # from the target toward the camera
UP = Vector((0, -math.sin(ELEV), math.cos(ELEV)))
RIGHT = Vector((1, 0, 0))
ORTHO = float(OPT.get('ortho', 5.6))                     # frame width in scene units
VC = float(OPT.get('vc', -0.25))                         # image height of the frame centre
PX = ORTHO / 3840                                        # one 4K pixel in scene units

def curve_object(name, collection, polylines, mat, cyclic):
    """One curve object, many POLY splines. polylines: list of (points, radius_factor)."""
    cu = bpy.data.curves.new(name, 'CURVE')
    cu.dimensions = '3D'
    cu.bevel_depth = PX              # radius factor 1 = one 4K pixel of half-width
    cu.bevel_resolution = 3
    cu.use_fill_caps = True
    for pts, rad in polylines:
        sp = cu.splines.new('POLY')
        sp.points.add(len(pts) - 1)
        flat = []
        for p in pts:
            flat.extend((p[0], p[1], p[2], 1.0))
        sp.points.foreach_set('co', flat)
        sp.points.foreach_set('radius', [rad] * len(pts))
        sp.use_cyclic_u = cyclic
    ob = bpy.data.objects.new(name, cu)
    collection.objects.link(ob)
    cu.materials.append(mat)
    return ob

def ring_points(centre, radius, normal, px_per_seg=5.0):
    n = Vector(normal).normalized()
    e1 = n.cross(Vector((1, 0, 0)))
    if e1.length < 1e-6:
        e1 = n.cross(Vector((0, 1, 0)))
    e1.normalize()
    e2 = n.cross(e1)
    segs = max(48, int(2 * math.pi * radius / (px_per_seg * PX)))
    c = Vector(centre)
    return [tuple(c + radius * (math.cos(2 * math.pi * i / segs) * e1 + math.sin(2 * math.pi * i / segs) * e2))
            for i in range(segs)]

def plane_ring(pl):
    n = [float(x) for x in pl[0]]
    d = float(pl[1])
    nn = sum(x * x for x in n)
    centre = [d * x / nn for x in n]
    return centre, math.sqrt(1 - d * d / nn), n

def width_for(radius, base):
    # Lines keep their house weight; a ring smaller than about 40 of its own widths thins with it.
    return min(base, radius / (40 * PX))

W_ROW, W_NEST, W_BOUND = 1.7, 1.25, 1.0      # half-widths in 4K pixels

# Floor.
U = 40.0
curve_object('floor / row of equal circles r = 1/2 on v = 8/5', C_FLOOR,
             [(ring_points((float(a), float(b), 0.0), float(RHO), (0, 0, 1)), W_ROW) for a, b in ROW],
             ROUTE, True)
curve_object('floor / parallel lines v = 21/10 + j', C_FLOOR,
             [([(-U, float(y), 0.0), (U, float(y), 0.0)], W_NEST) for y in LINES[1:]], PALE, False)
curve_object('floor / strip boundaries v = 11/10, 21/10', C_FLOOR,
             [([(-U, float(y), 0.0), (U, float(y), 0.0)], W_BOUND) for y in (OUTER, INNER)], DIM, False)

# Dome.
rings = []
for pl in CHAIN:
    c, r, n = plane_ring(pl)
    rings.append((ring_points(c, r, n), width_for(r, W_ROW)))
curve_object('dome / chain of tangent circles shrinking toward N', C_DOME, rings, ROUTE, True)
rings = []
for pl in NESTED[1:]:
    c, r, n = plane_ring(pl)
    rings.append((ring_points(c, r, n), width_for(r, W_NEST)))
curve_object('dome / nested circles touching at N', C_DOME, rings, PALE, True)
rings = []
for pl in (BOUND_OUT, BOUND_IN):
    c, r, n = plane_ring(pl)
    rings.append((ring_points(c, r, n), width_for(r, W_BOUND)))
curve_object('dome / boundary circles of the crescent', C_DOME, rings, DIM, True)

# Diamonds (octahedra facing the camera), the house node.
def diamonds(name, collection, items, mat):
    verts, faces = [], []
    for pos, r in items:
        p = Vector(pos)
        base = len(verts)
        for off in (r * RIGHT, -r * RIGHT, .57 * r * VIEW, -.57 * r * VIEW, r * UP, -r * UP):
            verts.append(tuple(p + off))
        for f in ((0, 2, 4), (2, 1, 4), (1, 3, 4), (3, 0, 4), (2, 0, 5), (1, 2, 5), (3, 1, 5), (0, 3, 5)):
            faces.append(tuple(base + i for i in f))
    me = bpy.data.meshes.new(name)
    me.from_pydata(verts, [], faces)
    me.update()
    ob = bpy.data.objects.new(name, me)
    collection.objects.link(ob)
    me.materials.append(mat)
    return ob

D_NODE = 8.0 * PX
diamonds('floor / contact points of the row', C_FLOOR,
         [((float(u), float(v), 0.0), D_NODE) for u, v in CONTACTS], INK)
items = []
for i, c in enumerate(CONTACTS):
    P = [float(x) for x in lift(c)]
    r_small = min(plane_ring(CHAIN[i])[1], plane_ring(CHAIN[i + 1])[1])
    items.append((P, min(D_NODE, .22 * r_small)))
diamonds('dome / contact points of the chain', C_DOME, items, INK)
diamonds('N / the touching point', C_POINT, [((0.0, 0.0, 1.0), 17.0 * PX)], GOLD)

# Lines of sight from N, drawn from where each leaves the dome to where it meets the floor
# (the part from N to the dome lies inside the sphere).
if OPT.get('rays', '1') == '1':
    THREAD = emission('line of sight from N / thread', (.18, .44, .49), .48)
    curve_object('N / lines of sight through the contact points', C_POINT,
                 [([tuple(float(x) for x in lift(c)), (float(c[0]), float(c[1]), 0.0)], .55) for c in CONTACTS],
                 THREAD, False)

# Ground and camera.
me = bpy.data.meshes.new('Backdrop / graphite')
S_ = 400.0
me.from_pydata([(-S_, -S_, -.05), (S_, -S_, -.05), (S_, S_, -.05), (-S_, S_, -.05)], [], [(0, 1, 2, 3)])
ground = bpy.data.objects.new('Backdrop / graphite', me)
C_STAGE.objects.link(ground)
me.materials.append(GROUND)

cam_data = bpy.data.cameras.new('Plate / orthographic')
cam_data.type = 'ORTHO'
cam_data.ortho_scale = ORTHO
cam_data.clip_start = .1
cam_data.clip_end = 400
camera = bpy.data.objects.new('Plate / orthographic', cam_data)
C_STAGE.objects.link(camera)
target = VC * UP
camera.location = target + 60 * VIEW
camera.rotation_euler = (-VIEW).to_track_quat('-Z', 'Y').to_euler()
scene.camera = camera

# Provenance inside the .blend.
tx = bpy.data.texts.new('EVIDENCE.json')
tx.write(json.dumps(evidence, indent=2, ensure_ascii=False))
readme = bpy.data.texts.new('SCENE_STRUCTURE')
readme.write('Floor: parallel lines v = 21/10 + j and one row of equal circles of radius 1/2 on v = 8/5. '
             'Dome: the same picture under inversion in N = (0,0,1) with radius sqrt 2, that is circles touching '
             'at N and a chain of tangent circles shrinking toward N. N is the point at infinity of the floor. '
             'All facts are asserted in exact arithmetic before rendering; see EVIDENCE.json.\n')
scene['author'] = 'lmtlssss🜐'
scene['figure'] = 'The Unifier, cover'
scene['exact_data_sha256'] = evidence['exact_data_sha256']
scene['facts'] = ', '.join(f['id'] for f in facts)

if OPT.get('save', '1' if OUTPUT.name == '00-cover-4k.png' else '0') == '1':
    try:
        bpy.ops.file.pack_all()
    except Exception:
        pass
    blend = ROOT / 'unifier-cover.blend'
    bpy.ops.wm.save_as_mainfile(filepath=str(blend), compress=True)
    print('BLEND', blend, flush=True)

t0 = time.time()
bpy.ops.render.render(write_still=True)
print('RENDER_SECONDS %.1f' % (time.time() - t0), flush=True)
assert OUTPUT.is_file()
print('RENDER_COMPLETE', OUTPUT, WIDTH, HEIGHT, flush=True)
