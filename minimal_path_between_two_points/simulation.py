"""Visual check of the shortest-path theorem. Stdlib only.

    python3 simulation.py   ->  writes simulation.svg and prints a table

Left panel (R^2): random paths from a=(0,0) to b=(3,4). Every one is longer
than the straight line, whose length is 5 (Theorem 5.2).

Right panel (Q^2): the two-step paths Q_t from Prop. 6.1, from (0,0) to (1,1),
computed with exact fractions. Their lengths 10/7, 58/41, ... keep shrinking
toward sqrt(2) but never reach it, so Q^2 has no shortest path.
"""
import math
import random
from fractions import Fraction as Fr
from pathlib import Path


def length(path):
    return sum(math.dist(p, q) for p, q in zip(path, path[1:]))


# --- R^2: random paths are never shorter than the straight line -------------
random.seed(1)
A, B = (0.0, 0.0), (3.0, 4.0)
D = math.dist(A, B)
random_paths = [
    [A, *[(random.uniform(-1, 4), random.uniform(-1, 5)) for _ in range(random.randint(1, 4))], B]
    for _ in range(25)
]
for P in random_paths:
    assert length(P) >= D


# --- Q^2: paths Q_t, exact arithmetic (paper, Prop. 6.1 Steps 3-4) -----------
def Q(t):
    """Two-step path (0,0) -> c -> (1,1), with its exact rational length."""
    D = 1 + 2 * t - t * t
    c = ((1 - t * t) / D, 2 * t / D)
    step = (1 + t * t) / D  # each step has this exact length
    assert c[0] ** 2 + c[1] ** 2 == step**2
    assert (1 - c[0]) ** 2 + (1 - c[1]) ** 2 == step**2
    return [(Fr(0), Fr(0)), c, (Fr(1), Fr(1))], 2 * step


rows, p, r = [], 3, 2  # Pell numbers: p/r -> sqrt(2)
for m in range(1, 7):
    path, L = Q(Fr(p, r) - 1)
    rows.append((path, L))
    p, r = p + 2 * r, p + r
lengths = [L for _, L in rows]
assert all(L * L > 2 for L in lengths)  # never reaches sqrt(2) ...
assert all(x > y for x, y in zip(lengths, lengths[1:]))  # ... but keeps getting shorter

print(f"R^2: {len(random_paths)} random paths, shortest {min(map(length, random_paths)):.4f} >= {D}")
print("Q^2: two-step paths (0,0) -> c -> (1,1)")
for path, L in rows:
    print(f"  c = ({str(path[1][0]):>12}, {str(path[1][1]):>12})  L = {str(L):>12} = {float(L):.10f}")
print(f"  sqrt(2) = {math.sqrt(2):.10f}")


# --- draw -------------------------------------------------------------------
def panel(x0, box, paths, line, title, note):
    """SVG group: box = (xmin, xmax, ymin, ymax) mapped to a 360x360 square."""
    xmin, xmax, ymin, ymax = box
    sx = lambda x: x0 + 20 + 360 * (float(x) - xmin) / (xmax - xmin)
    sy = lambda y: 400 - 360 * (float(y) - ymin) / (ymax - ymin)
    pts = lambda P: " ".join(f"{sx(x):.1f},{sy(y):.1f}" for x, y in P)
    out = [f'<rect x="{x0 + 20}" y="40" width="360" height="360" fill="none" stroke="#ccc"/>',
           f'<text x="{x0 + 200}" y="25" text-anchor="middle" font-weight="bold">{title}</text>',
           f'<text x="{x0 + 200}" y="425" text-anchor="middle">{note}</text>']
    for P, color in paths:
        out.append(f'<polyline points="{pts(P)}" fill="none" stroke="{color}" stroke-width="1.2"/>')
        if len(P) == 3:  # mark the corner c of a two-step path
            out.append(f'<circle cx="{sx(P[1][0]):.1f}" cy="{sy(P[1][1]):.1f}" r="3.5" fill="{color}"/>')
    out.append(f'<polyline points="{pts(line)}" fill="none" stroke="crimson" stroke-width="2" stroke-dasharray="6 4"/>')
    return "\n".join(out)


blues = ["#9ecae1", "#6baed6", "#4292c6", "#2171b5", "#08519c", "#08306b"]
svg = f"""<svg xmlns="http://www.w3.org/2000/svg" width="820" height="440" font-family="sans-serif" font-size="13">
<rect width="100%" height="100%" fill="white"/>
{panel(0, (-1, 4, -1, 5), [(P, "#bbb") for P in random_paths], [A, B],
       "R²: every path ≥ straight line", f"dashed red = straight line, length {D:g}")}
{panel(410, (0, 1, 0, 1), [(P, c) for (P, _), c in zip(rows, blues)], [(0, 0), (1, 1)],
       "Q²: no shortest path", "lengths 10/7, 58/41, … → √2, never reached")}
</svg>"""
out = Path(__file__).with_name("simulation.svg")
out.write_text(svg)
print(f"wrote {out}")
