"""Visualization for Rosen Ch. 10, Supplementary Exercise 41:  deg⁻(v) + deg⁺(v) = n − 1.

    "What is the sum of the in-degree and out-degree of a vertex in a tournament?"

Answer: n − 1, where n is the number of vertices. An EDUCATIONAL COMPANION to the Lean
theorem `GraphCh10.supp41` (GraphCh10/Exercises/Supp41.lean), for students learning Lean 4
and introductory graph theory. It has two parts:

1. A static summary figure (visualizations/supp41.png).
2. An interactive explorer: click a vertex to see its incoming and outgoing arrows and a
   "ledger" showing what every other vertex adds to in-degree + out-degree; click an arrow
   to reverse it; change the number of vertices; break one rule of "tournament" at a time
   to see what goes wrong; and step through the actual Lean proof with Previous/Next.
   Each step explains the mathematics and the Lean tactics and highlights the matching
   vertices and arrows. The Lean code shown is read from the project files at runtime.

Like Exercise 9(a), this is a "for every" theorem: every picture here is ONE tournament and
only illustrates the statement. The script also checks every tournament with up to 6
vertices, which is still evidence, not a proof. The general statement, for every finite
tournament and every vertex, is established by the Lean proof.

The graph model follows GraphCh10/Definitions.lean exactly:

* `DGraph V E` -- vertices V, edges E, and `ends : E → V × V`, the ordered pair
  (initial vertex, terminal vertex) of each edge. Here `ends[e]` is a tuple (u, w).
* `DAdj u w := ∃ e, G.ends e = (u, w)`              -- `d_adj(u, w)`: (u, w) is an edge.
* `inDeg v  := #{e | (G.ends e).2 = v}`              -- `in_deg(v)`.
* `outDeg v := #{e | (G.ends e).1 = v}`              -- `out_deg(v)`.
* `IsLoop e := (G.ends e).1 = (G.ends e).2`          -- `is_loop(e)`.
* `HasMultipleEdges := ∃ e₁ e₂, e₁ ≠ e₂ ∧ ends e₁ = ends e₂`.
* `IsSimple := ¬ HasMultipleEdges ∧ ∀ e, ¬ IsLoop e`.
* `IsTournament := IsSimple ∧ ∀ u w, u ≠ w → Xor (DAdj u w) (DAdj w u)`.

Every degree is COMPUTED from `ends` with these definitions; none is hardcoded.

Run (from the project root):
    python -m pip install networkx matplotlib
    python visualizations/supp41.py              # save the PNG, then open the explorer
    python visualizations/supp41.py --static     # only checks + PNG (no window)
    python visualizations/supp41.py --snapshots DIR
        # headless self-test: drives the explorer through every walkthrough step,
        # simulates mouse clicks, and saves one PNG per step into DIR

Explorer controls:
    click a vertex          choose the vertex v (its arrows: orange = out, purple = in)
    click an arrow          reverse its direction (the graph stays a tournament)
    n − / +                 fewer / more vertices (a new tournament is generated)
    Random tournament       another tournament with the same number of vertices
    Reset to the example    the 5-vertex example the walkthrough starts with
    Break a rule at v       add a loop / copy an arrow / add the reverse arrow / delete an
                            arrow at v -- the graph is then NOT a tournament
    ◀ Previous / Next ▶     move through the walkthrough (also ← / → keys)
    Next example            show another vertex / arrow / pair for the current step
"""

from __future__ import annotations

import argparse
import math
import random
import re
import sys
import textwrap
from itertools import combinations, product
from pathlib import Path

import matplotlib

# Pick a file-only backend before pyplot is imported when no window will be opened.
if "--static" in sys.argv or "--snapshots" in sys.argv:
    matplotlib.use("Agg")

import matplotlib.patheffects as pe
import matplotlib.pyplot as plt
import networkx as nx
from matplotlib.backend_bases import MouseEvent
from matplotlib.gridspec import GridSpec, GridSpecFromSubplotSpec
from matplotlib.lines import Line2D
from matplotlib.patches import Circle, FancyArrowPatch, FancyBboxPatch, Patch
from matplotlib.widgets import Button

PROJECT_ROOT = Path(__file__).resolve().parent.parent
PROOF_FILE = PROJECT_ROOT / "GraphCh10" / "Exercises" / "Supp41.lean"
DEFS_FILE = PROJECT_ROOT / "GraphCh10" / "Definitions.lean"
LEMMAS_FILE = PROJECT_ROOT / "GraphCh10" / "Lemmas.lean"
TESTS_FILE = PROJECT_ROOT / "GraphCh10" / "DefinitionTests.lean"

# The theorem statement approved by the project owner (checked against the Lean file).
APPROVED_STATEMENT = [
    "theorem supp41 {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]",
    "    (G : DGraph V E) (hG : G.IsTournament) (v : V) :",
    "    G.inDeg v + G.outDeg v = Fintype.card V - 1 := by",
]

Ends = dict[str, tuple[int, int]]


def _require(path: Path) -> list[str]:
    if not path.exists():
        sys.exit(f"error: cannot find {path}; run this script inside the GraphCh10 project")
    return path.read_text(encoding="utf-8").splitlines()


# ---------------------------------------------------------------------------
# 1. The definitions, mirroring GraphCh10/Definitions.lean
# ---------------------------------------------------------------------------

def d_adj(ends: Ends, u: int, w: int) -> bool:
    """`DAdj u w := ∃ e : E, G.ends e = (u, w)`: (u, w) is an edge."""
    return any(p == (u, w) for p in ends.values())


def out_edges(ends: Ends, v: int) -> list[str]:
    """The edges counted by `outDeg v`: those with initial vertex v."""
    return [e for e, p in ends.items() if p[0] == v]


def in_edges(ends: Ends, v: int) -> list[str]:
    """The edges counted by `inDeg v`: those with terminal vertex v."""
    return [e for e, p in ends.items() if p[1] == v]


def out_deg(ends: Ends, v: int) -> int:
    """`outDeg v := (Finset.univ.filter (fun e => (G.ends e).1 = v)).card`."""
    return len(out_edges(ends, v))


def in_deg(ends: Ends, v: int) -> int:
    """`inDeg v := (Finset.univ.filter (fun e => (G.ends e).2 = v)).card`."""
    return len(in_edges(ends, v))


def is_loop(ends: Ends, e: str) -> bool:
    """`IsLoop e := (G.ends e).1 = (G.ends e).2`."""
    return ends[e][0] == ends[e][1]


def multiple_edge_pairs(ends: Ends) -> list[tuple[str, str]]:
    """Witnesses of `HasMultipleEdges`: distinct edges e₁, e₂ with the same ordered pair."""
    return [(a, b) for a, b in combinations(ends, 2) if ends[a] == ends[b]]


def is_simple(ends: Ends) -> bool:
    """`IsSimple := ¬ G.HasMultipleEdges ∧ ∀ e : E, ¬ G.IsLoop e`."""
    return not multiple_edge_pairs(ends) and not any(is_loop(ends, e) for e in ends)


def xor_fails(ends: Ends, vs: list[int]) -> list[tuple[int, int, int]]:
    """Pairs u < w where `Xor (DAdj u w) (DAdj w u)` fails: (u, w, #directions present)."""
    return [(u, w, d_adj(ends, u, w) + d_adj(ends, w, u)) for u, w in combinations(vs, 2)
            if d_adj(ends, u, w) == d_adj(ends, w, u)]


def is_tournament(ends: Ends, vs: list[int]) -> bool:
    """`IsTournament := G.IsSimple ∧ ∀ u w, u ≠ w → Xor (G.DAdj u w) (G.DAdj w u)`."""
    return is_simple(ends) and not xor_fails(ends, vs)


def out_nbrs(ends: Ends, v: int, vs: list[int]) -> list[int]:
    """`Finset.univ.filter (fun w => G.DAdj v w)`: the out-neighbours of v."""
    return [w for w in vs if d_adj(ends, v, w)]


def in_nbrs(ends: Ends, v: int, vs: list[int]) -> list[int]:
    """`Finset.univ.filter (fun w => G.DAdj w v)`: the in-neighbours of v."""
    return [w for w in vs if d_adj(ends, w, v)]


def broken_reasons(ends: Ends, vs: list[int]) -> list[str]:
    """Why the graph is not a tournament (empty list when it is one)."""
    out = []
    loops = sorted({ends[e][0] for e in ends if is_loop(ends, e)})
    if loops:
        out.append("a loop at " + ", ".join(map(str, loops)))
    mult = sorted({ends[a] for a, _b in multiple_edge_pairs(ends)})
    if mult:
        out.append("multiple edges " + ", ".join(f"({u}, {w})" for u, w in mult))
    for u, w, k in xor_fails(ends, vs):
        out.append(f"arrows both ways between {u} and {w}" if k == 2
                   else f"no arrow between {u} and {w}")
    return out


# ---------------------------------------------------------------------------
# 2. Examples: the explorer's 5-vertex tournament and the Lean test graphs
# ---------------------------------------------------------------------------

def as_map(pairs: list[tuple[int, int]]) -> Ends:
    """Edge i is named e{i} (edge `i : Fin m` in Lean)."""
    return {f"e{i}": p for i, p in enumerate(pairs)}


# The explorer's starting example: a 5-vertex tournament chosen so that the degrees vary
# (vertex 0 beats everyone, so in(0) = 0). It is an illustration only, defined here.
EXAMPLE_N = 5
EXAMPLE_ENDS: Ends = as_map([(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (4, 1), (2, 3),
                             (4, 2), (3, 4)])
EXAMPLE_START_V = 1

DGRAPH_DEF = re.compile(r"^def (\w+) : DGraph \(Fin (\d+)\) \((Fin (\d+)|Empty)\) :=(.*)$")


def parse_test_dgraph(name: str) -> tuple[list[int], Ends, str]:
    """Rebuild a `DGraph (Fin n) (Fin m)` test graph from GraphCh10/DefinitionTests.lean.

    The bodies have the shape `⟨fun e => if e = 0 then (a, b) else if e = 1 then … else (c, d)⟩`
    or `⟨fun _ => (a, b)⟩`: edge i gets the i-th pair, the edges after the last `if` get the
    final `else` pair."""
    lines = _require(TESTS_FILE)
    hits = [i for i, ln in enumerate(lines) if ln.startswith(f"def {name} : DGraph")]
    assert len(hits) == 1, f"expected exactly one `def {name}` in DefinitionTests.lean"
    body_lines = [lines[hits[0]]]
    for ln in lines[hits[0] + 1:]:
        if not ln.strip():
            break
        body_lines.append(ln)
    m = DGRAPH_DEF.match(body_lines[0])
    assert m, f"`def {name}` has an unexpected shape"
    n_v = int(m.group(2))
    n_e = 0 if m.group(3) == "Empty" else int(m.group(4))
    body = " ".join(body_lines)[len(m.group(0)) - len(m.group(5)):]
    pairs = [(int(a), int(b)) for a, b in re.findall(r"\((\d+), (\d+)\)", body)]
    conds = re.findall(r"if e = (\d+)", body)
    assert conds == [str(i) for i in range(len(pairs) - 1)], f"unexpected `if` chain in {name}"
    ends = {f"e{i}": pairs[min(i, len(pairs) - 1)] for i in range(n_e)}
    return list(range(n_v)), ends, " ".join(ln.strip() for ln in body_lines)


TEST_GRAPHS = {name: parse_test_dgraph(name) for name in ("cyc3", "tr3", "dloop", "dup", "both")}
# A "missing arrow" example is not among the Lean test graphs; it is defined here.
MISSING = ([0, 1, 2], as_map([(0, 1), (1, 2)]))


def tournament_from_bits(n: int, bits) -> Ends:
    """The tournament on 0..n-1 where pair (u, w), u < w, points u → w iff its bit is 0."""
    return as_map([(u, w) if b == 0 else (w, u)
                   for (u, w), b in zip(combinations(range(n), 2), bits)])


def all_tournaments(n: int):
    k = n * (n - 1) // 2
    for bits in product((0, 1), repeat=k):
        yield tournament_from_bits(n, bits)


# ---------------------------------------------------------------------------
# 3. Programmatic checks
# ---------------------------------------------------------------------------

def check_statement() -> None:
    """The Lean file still contains exactly the approved theorem statement."""
    lines = _require(PROOF_FILE)
    i = next(i for i, ln in enumerate(lines) if ln.startswith("theorem supp41"))
    assert lines[i:i + 3] == APPROVED_STATEMENT, "the statement of supp41 has changed"


def run_checks() -> dict:
    """Assert every fact the pictures and the walkthrough rely on. Returns summary numbers."""
    check_statement()
    vs = list(range(EXAMPLE_N))
    # The example is a tournament, and the formula holds at every vertex.
    assert is_tournament(EXAMPLE_ENDS, vs)
    assert len(EXAMPLE_ENDS) == EXAMPLE_N * (EXAMPLE_N - 1) // 2
    for v in vs:
        assert in_deg(EXAMPLE_ENDS, v) + out_deg(EXAMPLE_ENDS, v) == EXAMPLE_N - 1
    # It is informative: the degrees vary and the starting vertex has both kinds of arrows.
    assert len({out_deg(EXAMPLE_ENDS, v) for v in vs}) >= 3
    assert in_deg(EXAMPLE_ENDS, EXAMPLE_START_V) > 0 and out_deg(EXAMPLE_ENDS, EXAMPLE_START_V) > 0

    # Cross-check in/out-degrees with NetworkX's MultiDiGraph.
    G = nx.MultiDiGraph()
    G.add_nodes_from(vs)
    G.add_edges_from(EXAMPLE_ENDS.values())
    assert all(G.in_degree(v) == in_deg(EXAMPLE_ENDS, v) and
               G.out_degree(v) == out_deg(EXAMPLE_ENDS, v) for v in vs)

    # The Lean test graphs: tournaments where Lean says so, and the formula's behaviour.
    for name, expect in (("cyc3", True), ("tr3", True), ("dloop", False), ("dup", False),
                         ("both", False)):
        tv, te, _src = TEST_GRAPHS[name]
        assert is_tournament(te, tv) == expect, name
    assert not is_tournament(*MISSING[::-1])

    # Every tournament on 1..6 vertices: each step of the proof, at every vertex.
    n_tour = 0
    for n in range(1, 7):
        vs_n = list(range(n))
        others_all = {v: [w for w in vs_n if w != v] for v in vs_n}
        for t in all_tournaments(n):
            n_tour += 1
            assert is_tournament(t, vs_n)
            for v in vs_n:
                outs, ins = out_nbrs(t, v, vs_n), in_nbrs(t, v, vs_n)
                others = others_all[v]
                assert out_deg(t, v) == len(outs)              # helper A
                assert in_deg(t, v) == len(ins)                # helper B
                assert not d_adj(t, v, v)                      # helper C
                assert outs == [w for w in others if d_adj(t, v, w)]          # hOut
                assert ins == [w for w in others if not d_adj(t, v, w)]       # hIn
                assert in_deg(t, v) + out_deg(t, v) == n - 1                  # supp41

    # Breaking each rule can break the formula (one example each, at vertex 0).
    broken = {}
    for name in ("dloop", "dup", "both"):
        tv, te, _src = TEST_GRAPHS[name]
        broken[name] = in_deg(te, 0) + out_deg(te, 0)
        assert broken[name] != len(tv) - 1, name
    assert in_deg(MISSING[1], 0) + out_deg(MISSING[1], 0) != len(MISSING[0]) - 1
    # ... and in `dup` the two counts of helper A really differ (why hinj needs simplicity).
    tv, te, _src = TEST_GRAPHS["dup"]
    assert out_deg(te, 0) == 2 and len(out_nbrs(te, 0, tv)) == 1
    return dict(n_tour=n_tour)


# ---------------------------------------------------------------------------
# 4. Shared drawing helpers
# ---------------------------------------------------------------------------

COLOR_VERTEX = "#3B6FB6"   # blue vertex fill
COLOR_OUT = "#E08A2C"      # orange: an arrow LEAVING the chosen vertex v (counts in outDeg)
COLOR_IN = "#7B3FB8"       # purple: an arrow ENTERING the chosen vertex v (counts in inDeg)
COLOR_LOOP = "#9A2A2A"     # dark red: a loop (not allowed)
COLOR_OK = "#1E8C45"       # green: a check that holds
COLOR_FOCUS = "#F2B705"    # gold: the vertex / arrow the current walkthrough step is about
COLOR_EDGE = "#B8B8B8"     # an arrow not touching v
COLOR_TEXT = "#222222"
COLOR_WARN = "#9A2A2A"
COLOR_CODE_BG = "#FBFBF8"
COLOR_CODE_HL = "#FFF1B8"

NODE_R = 0.27  # node radius in data units
RING = 1.9     # vertices sit on a circle of this radius


def positions(n: int) -> dict[int, tuple[float, float]]:
    """Vertices evenly spaced on a circle, vertex 0 at the top, going clockwise."""
    if n == 1:
        return {0: (0.0, 0.0)}
    return {i: (RING * math.sin(2 * math.pi * i / n), RING * math.cos(2 * math.pi * i / n))
            for i in range(n)}


def outward(pos: tuple[float, float]) -> tuple[float, float]:
    x, y = pos
    r = math.hypot(x, y)
    return (0.0, 1.0) if r < 1e-9 else (x / r, y / r)


def edge_rad(ends: Ends, e: str) -> float:
    """Curvature: arrows sharing the same two endpoints (either direction) are drawn apart."""
    u, w = ends[e]
    key = frozenset((u, w))
    group = [x for x in ends if frozenset(ends[x]) == key]
    if len(group) == 1:
        return 0.0
    k = group.index(e)
    rad = (k - (len(group) - 1) / 2) * 0.32
    return rad if u < w else -rad  # same visual side for both directions, then spread


def edge_curve(pos, ends: Ends, e: str, n_pts: int = 24) -> list[tuple[float, float]]:
    """Points along the drawn arrow (the quadratic Bézier used by arc3), for click tests."""
    u, w = ends[e]
    (x1, y1), (x2, y2) = pos[u], pos[w]
    rad = edge_rad(ends, e)
    cx, cy = (x1 + x2) / 2 + rad * (y2 - y1), (y1 + y2) / 2 - rad * (x2 - x1)
    pts = []
    for i in range(n_pts + 1):
        t = 0.15 + 0.7 * i / n_pts  # stay away from the vertex discs
        pts.append(((1 - t) ** 2 * x1 + 2 * (1 - t) * t * cx + t ** 2 * x2,
                    (1 - t) ** 2 * y1 + 2 * (1 - t) * t * cy + t ** 2 * y2))
    return pts


def v_colors(ends: Ends, v: int | None) -> dict[str, str]:
    """Orange for arrows leaving v, purple for arrows entering v, red for loops at v."""
    if v is None:
        return {}
    cols = {}
    for e, (a, b) in ends.items():
        if a == v and b == v:
            cols[e] = COLOR_LOOP
        elif a == v:
            cols[e] = COLOR_OUT
        elif b == v:
            cols[e] = COLOR_IN
    return cols


def draw_graph(ax, ends: Ends, vs: list[int], edge_colors: dict[str, str] | None = None,
               emphasized: frozenset[str] = frozenset(), tags: dict[int, str] | None = None,
               badges: bool = True, chosen: int | None = None, labels: bool = True,
               r: float = NODE_R, fontsize: float = 14, width: float = 2.6,
               shrink: float = 16, mscale: float = 18) -> None:
    """Draw arrows and vertices. Arrows coloured by `edge_colors` (others grey) get their edge
    name; `emphasized` arrows are drawn extra thick with a dark outline; `tags` adds a gold
    halo and a label; `badges` shows 'in a · out b' next to each vertex (bold for `chosen`)."""
    pos = positions(len(vs))
    edge_colors = edge_colors or {}
    tags = tags or {}
    for e, (u, w) in ends.items():
        color = edge_colors.get(e, COLOR_EDGE)
        lw, z, effects = width, 2, None
        if e in emphasized:
            lw, z = width * 1.6, 2.5
            effects = [pe.withStroke(linewidth=width * 2.8, foreground="#333333")]
        if u == w:  # loop: a dashed circle beside the vertex (rotated away from the badge)
            ox, oy = outward(pos[u])
            c, s_ = math.cos(math.radians(75)), math.sin(math.radians(75))
            dx, dy = c * ox - s_ * oy, s_ * ox + c * oy
            x, y = pos[u]
            patch = Circle((x + (r + 0.2) * dx, y + (r + 0.2) * dy), 0.22, fill=False,
                           edgecolor=edge_colors.get(e, COLOR_LOOP), linewidth=lw, zorder=z,
                           linestyle="--")
            lx, ly = x + (r + 0.62) * dx, y + (r + 0.62) * dy
        else:
            rad = edge_rad(ends, e)
            patch = FancyArrowPatch(pos[u], pos[w], arrowstyle="-|>", mutation_scale=mscale,
                                    connectionstyle=f"arc3,rad={rad}", color=color,
                                    linewidth=lw, shrinkA=shrink, shrinkB=shrink, zorder=z)
            pts = edge_curve(pos, ends, e)
            lx, ly = pts[len(pts) // 2]
        if effects:
            patch.set_path_effects(effects)
        ax.add_patch(patch)
        if labels and (e in edge_colors or e in emphasized):
            ax.text(lx, ly, e, fontsize=fontsize * 0.6, color="#333333", ha="center",
                    va="center", zorder=3, bbox=dict(boxstyle="round,pad=0.12", fc="white",
                                                     ec="none", alpha=0.9))
    for v in vs:
        x, y = pos[v]
        if v in tags:
            ax.add_patch(Circle((x, y), r + 0.15, facecolor=COLOR_FOCUS, alpha=0.6,
                                edgecolor="none", zorder=3.5))
        ax.add_patch(Circle((x, y), r, facecolor=COLOR_VERTEX, edgecolor="#2A4F85",
                            linewidth=1.5, zorder=4))
        ax.text(x, y, str(v), ha="center", va="center", fontsize=fontsize, fontweight="bold",
                color="white", zorder=5)
        dx, dy = outward(pos[v])
        if badges:
            bold = v == chosen
            bx, by = x + dx * (r + 0.5), y + dy * (r + 0.42)
            if len(vs) == 1:
                bx, by = x, y - r - 0.4
            ax.text(bx, by, f"in {in_deg(ends, v)} · out {out_deg(ends, v)}", ha="center",
                    va="center", fontsize=fontsize * (0.66 if bold else 0.58),
                    fontweight="bold" if bold else "normal", zorder=6, color=COLOR_TEXT,
                    bbox=dict(boxstyle="round,pad=0.2", fc="#FFF4C2" if bold else "white",
                              ec=COLOR_FOCUS if bold else "#CCCCCC"))
        if v in tags:
            tx, ty = x - dx * (r + 0.32), y - dy * (r + 0.32)  # inside the ring
            if len(vs) == 1:
                tx, ty = x + r + 0.35, y
            ax.text(tx, ty, tags[v], ha="center", va="center", fontsize=fontsize * 0.68,
                    fontweight="bold", color="#5A4500", zorder=6,
                    bbox=dict(boxstyle="round,pad=0.15", fc="#FFF4C2", ec=COLOR_FOCUS))


def frame(ax, xlim=(-3.3, 3.3), ylim=(-2.75, 2.75)) -> None:
    ax.set_xlim(*xlim)
    ax.set_ylim(*ylim)
    ax.set_aspect("equal")
    ax.axis("off")


def fmt_pairs(ends: Ends, es: list[str]) -> str:
    return ", ".join(f"{u}→{w}" for u, w in (ends[e] for e in es)) or "none"


def deg_formula(ends: Ends, v: int, vs: list[int]) -> str:
    o, i = out_edges(ends, v), in_edges(ends, v)
    s = (f"v = {v}:  out-degree {len(o)} ({fmt_pairs(ends, o)}),  "
         f"in-degree {len(i)} ({fmt_pairs(ends, i)});  in + out = {len(o) + len(i)}")
    return s + f",  n − 1 = {len(vs) - 1}"


# ---------------------------------------------------------------------------
# 5. Static summary figure (visualizations/supp41.png)
# ---------------------------------------------------------------------------

def build_figure(stats: dict) -> plt.Figure:
    fig = plt.figure(figsize=(19, 14.5), facecolor="white")
    gs = GridSpec(3, 4, figure=fig, height_ratios=[0.95, 1.0, 0.62], hspace=0.32, wspace=0.08,
                  left=0.03, right=0.97, top=0.865, bottom=0.03)
    vs = list(range(EXAMPLE_N))

    fig.suptitle("Supplementary Exercise 41:  in-degree + out-degree = n − 1  in a tournament",
                 fontsize=19, fontweight="bold", color=COLOR_TEXT, y=0.985)
    fig.text(0.5, 0.956,
             "Question: \"What is the sum of the in-degree and out-degree of a vertex in a "
             "tournament?\"   Answer: n − 1 (n = number of vertices), proved in Lean as "
             "GraphCh10.supp41.", ha="center", fontsize=10.5, color="#444444")
    fig.text(0.5, 0.938,
             "Every picture below shows particular tournaments: they illustrate the theorem, "
             "they do not prove it. The Lean proof covers every finite tournament.  "
             "Run  python visualizations/supp41.py  for the interactive walkthrough.",
             ha="center", fontsize=10.5, color=COLOR_WARN, style="italic")

    # Row 0: the example, then three vertices with their in/out arrows.
    ax = fig.add_subplot(gs[0, 0])
    draw_graph(ax, EXAMPLE_ENDS, vs, labels=False)
    frame(ax)
    ax.set_title("An example tournament (5 vertices)", fontsize=13, fontweight="bold", pad=22)
    ax.text(0.5, 1.015, "every two vertices: exactly one arrow", transform=ax.transAxes,
            ha="center", va="bottom", fontsize=9.5, color="#444444")
    for col, v in enumerate((1, 0, 2)):
        ax = fig.add_subplot(gs[0, 1 + col])
        draw_graph(ax, EXAMPLE_ENDS, vs, v_colors(EXAMPLE_ENDS, v), tags={v: "v"}, chosen=v,
                   labels=False)
        frame(ax)
        i, o = in_deg(EXAMPLE_ENDS, v), out_deg(EXAMPLE_ENDS, v)
        ax.set_title(f"v = {v}:  in {i} + out {o} = {i + o} = 5 − 1", fontsize=13,
                     fontweight="bold", pad=22)
        ax.text(0.5, 1.015, f"purple in: {fmt_pairs(EXAMPLE_ENDS, in_edges(EXAMPLE_ENDS, v))}"
                f";  orange out: {fmt_pairs(EXAMPLE_ENDS, out_edges(EXAMPLE_ENDS, v))}",
                transform=ax.transAxes, ha="center", va="bottom", fontsize=9.3, color="#444444")

    # Row 1 left: the ledger for every vertex.
    ax = fig.add_subplot(gs[1, :2])
    ax.axis("off")
    rows = []
    for v in vs:
        outs, ins = out_nbrs(EXAMPLE_ENDS, v, vs), in_nbrs(EXAMPLE_ENDS, v, vs)
        others = [w for w in vs if w != v]
        rows.append([str(v), "{" + ", ".join(map(str, others)) + "}",
                     "{" + ", ".join(map(str, outs)) + "}" if outs else "none",
                     "{" + ", ".join(map(str, ins)) + "}" if ins else "none",
                     f"{len(ins)} + {len(outs)} = {len(ins) + len(outs)}", "✓"])
    table = ax.table(cellText=rows, colLabels=["v", "others (V without v)", "out-nbrs (v→w)",
                                               "in-nbrs (w→v)", "in + out", "= n − 1"],
                     loc="center", cellLoc="center", colWidths=[0.07, 0.22, 0.19, 0.19, 0.17, 0.1])
    table.auto_set_font_size(False)
    table.set_fontsize(11)
    table.scale(1, 2.1)
    for (r, c), cell in table.get_celld().items():
        cell.set_edgecolor("#CCCCCC")
        if r == 0:
            cell.set_facecolor("#EFEFEF")
            cell.set_text_props(fontweight="bold")
        elif c == 2:
            cell.set_text_props(color=COLOR_OUT, fontweight="bold")
        elif c == 3:
            cell.set_text_props(color=COLOR_IN, fontweight="bold")
        elif c == 5:
            cell.set_text_props(color=COLOR_OK, fontweight="bold")
    ax.set_title("The ledger: out-nbrs and in-nbrs split the other vertices (computed)",
                 fontsize=13, fontweight="bold", pad=22)
    ax.text(0.5, 1.015, "each other vertex is in exactly one of the two groups, so the two "
            "counts add up to n − 1 = 4", transform=ax.transAxes, ha="center", va="bottom",
            fontsize=9.5, color="#444444")

    # Row 1 right: Lean test graphs -- two tournaments and graphs that break one rule each.
    sub = GridSpecFromSubplotSpec(3, 3, subplot_spec=gs[1, 2:], height_ratios=[0.25, 1, 1],
                                  wspace=0.05, hspace=0.6)
    minis = [("cyc3", "tournament (3-cycle)"), ("tr3", "tournament"),
             ("dloop", "loop → not simple"), ("dup", "multiple edges"),
             ("both", "arrows both ways"), ("missing", "missing arrow")]
    for i, (name, label) in enumerate(minis):
        a = fig.add_subplot(sub[1 + i // 3, i % 3])
        mv, me = MISSING if name == "missing" else TEST_GRAPHS[name][:2]
        draw_graph(a, me, mv, v_colors(me, 0), tags={0: "v"}, chosen=0, labels=False,
                   badges=False, r=0.36, fontsize=11, width=2.0, shrink=12, mscale=13)
        frame(a, (-2.4, 2.4), (-2.3, 2.3))
        tot, target = in_deg(me, 0) + out_deg(me, 0), len(mv) - 1
        ok = tot == target
        a.set_title(f"{name}: {label}\nv = 0: in + out = {tot} {'=' if ok else '≠'} "
                    f"{target} = n − 1", fontsize=9.5, color=COLOR_OK if ok else COLOR_WARN,
                    pad=2)
    ax0 = fig.add_subplot(gs[1, 2:], frameon=False)
    ax0.set_xticks([])
    ax0.set_yticks([])
    ax0.set_title("Each rule of 'tournament' is needed", fontsize=13, fontweight="bold",
                  pad=22)
    ax0.text(0.5, 1.015, "first five graphs read from GraphCh10/DefinitionTests.lean; "
             "'missing' is defined in this script", transform=ax0.transAxes, ha="center",
             va="bottom", fontsize=9.5, color="#444444")

    # Row 2: proof correspondence.
    ax = fig.add_subplot(gs[2, :])
    ax.axis("off")
    ax.add_patch(plt.Rectangle((0, 0), 1, 1, transform=ax.transAxes, facecolor="#F7F7F7",
                               edgecolor="#D0D0D0", linewidth=1))
    left = ["The Lean proof, step by step  (GraphCh10/Exercises/Supp41.lean)",
            "lemma outDeg_eq_card_outNbrs   simple ⇒ deg⁺(v) = #{w | (v, w) is an edge}",
            "lemma inDeg_eq_card_inNbrs     simple ⇒ deg⁻(v) = #{w | (w, v) is an edge}",
            "lemma not_dAdj_self            simple ⇒ (v, v) is not an edge (no loops)",
            "obtain ⟨hSimple, hExactlyOne⟩  split the tournament hypothesis",
            "let others := univ.erase v     the n − 1 vertices other than v",
            "have hOut / have hIn           deg⁺ = #{w ∈ others | v→w},  deg⁻ = #{w ∈ others | ¬ v→w}",
            "calc …                         the two groups split others:  = #others = n − 1   (QED)"]
    right = ["Checked by assertions in this script",
             "• the theorem statement in Supp41.lean is the approved one",
             "• the example is a tournament; in + out = 4 at every vertex (and NetworkX agrees)",
             f"• all {stats['n_tour']:,} tournaments on 1 to 6 vertices: helpers A–C, hOut, hIn",
             "  and in + out = n − 1 hold at every vertex (evidence only, not a proof)",
             "• the Lean test graphs cyc3, tr3 are tournaments; dloop, dup, both are not,",
             "  and for them (and 'missing') in + out ≠ n − 1 at vertex 0"]
    for x, lines in ((0.015, left), (0.57, right)):
        ax.text(x, 0.92, lines[0], transform=ax.transAxes, fontsize=11.5, fontweight="bold",
                va="top", color=COLOR_TEXT)
        ax.text(x, 0.78, "\n".join(lines[1:]), transform=ax.transAxes, fontsize=9.8,
                va="top", color=COLOR_TEXT, family="DejaVu Sans Mono" if x < 0.5 else None,
                linespacing=1.55)

    legend = [
        Patch(facecolor=COLOR_VERTEX, edgecolor="#2A4F85", label="vertex"),
        Line2D([], [], color=COLOR_OUT, linewidth=3, label="arrow leaving v (out)"),
        Line2D([], [], color=COLOR_IN, linewidth=3, label="arrow entering v (in)"),
        Line2D([], [], color=COLOR_EDGE, linewidth=3, label="other arrow"),
        Line2D([], [], color=COLOR_LOOP, linewidth=3, linestyle="--", label="loop"),
        Patch(facecolor=COLOR_FOCUS, alpha=0.6, label="the chosen vertex v"),
    ]
    fig.legend(handles=legend, loc="upper center", ncol=6, frameon=False, fontsize=10,
               bbox_to_anchor=(0.5, 0.928))
    return fig


# ---------------------------------------------------------------------------
# 6. Lean source, read from the project (the source of truth)
# ---------------------------------------------------------------------------

def _block(lines: list[str], start: str, end: str) -> list[str]:
    """The lines from the unique line starting with `start` to the first later line
    containing `end` (inclusive)."""
    hits = [i for i, ln in enumerate(lines) if ln.strip().startswith(start)]
    assert len(hits) == 1, f"expected exactly one line starting with {start!r}"
    j = next(j for j in range(hits[0], len(lines)) if end in lines[j])
    return [ln.rstrip() for ln in lines[hits[0]:j + 1]]


def read_lean_sources() -> dict[str, list[str]]:
    """The proof of `supp41`, its helper lemmas and the definitions, read verbatim."""
    proof = _require(PROOF_FILE)
    lemmas = _require(LEMMAS_FILE)
    def_lines = _require(DEFS_FILE)

    def find(prefix: str, extra: int = 0) -> list[str]:
        hits = [i for i, ln in enumerate(def_lines) if ln.strip().startswith(prefix)]
        assert len(hits) == 1, f"expected exactly one line starting with {prefix!r}"
        return [ln.rstrip() for ln in def_lines[hits[0]:hits[0] + extra + 1]]

    defs = [
        "-- GraphCh10/Definitions.lean (excerpt; docstrings omitted)",
        *find("structure DGraph"),
        *find("ends : E → V × V"),
        "",
        "namespace DGraph   -- inside: variable (G : DGraph V E)",
        "",
        *find("def DAdj"),
        "",
        *find("def inDeg", extra=1),
        "",
        *find("def outDeg", extra=1),
        "",
        *find("def IsLoop (e : E) : Prop := (G.ends e).1"),  # DGraph's, not UGraph's
        "",
        *find("def HasMultipleEdges"),
        "",
        *find("def IsSimple"),
        "",
        *find("def IsTournament", extra=1),
    ]
    return {
        "defs": defs,
        "header": _block(proof, "**Answer: n − 1**", "deg⁻(v) + deg⁺(v) = n − 1."),
        "lemmas": ["-- GraphCh10/Lemmas.lean", "",
                   *_block(lemmas, "theorem ends_injective_of_isSimple",
                           "exact hG.1 ⟨e₁, e₂, hne, hends⟩")],
        "out": _block(proof, "theorem outDeg_eq_card_outNbrs", "by rw [himage]"),
        "in": _block(proof, "theorem inDeg_eq_card_inNbrs", "by rw [himage]"),
        "loop": _block(proof, "theorem not_dAdj_self", "exact hS.2 e"),
        "main": _block(proof, "theorem supp41", "rw [Finset.card_erase_of_mem"),
    }


SOURCE_NAMES = {
    "defs": "GraphCh10/Definitions.lean",
    "header": "Supp41.lean  ·  file comment",
    "lemmas": "GraphCh10/Lemmas.lean",
    "out": "Supp41.lean  ·  helper lemma A",
    "in": "Supp41.lean  ·  helper lemma B",
    "loop": "Supp41.lean  ·  helper lemma C",
    "main": "Supp41.lean  ·  the main theorem",
}


# ---------------------------------------------------------------------------
# 7. The walkthrough: graph basics, the proof idea, then the Lean proof
# ---------------------------------------------------------------------------
# Each step: part, title, which code to show, `anchors` (substrings that must each match
# exactly one line) and `ranges` ((first, last) substrings: every line in between is
# highlighted), a focus kind (what to highlight on the graph), and two explanations.
# `math` may be a function of (explorer, focus).

P1, P2, P3, P4, P5 = ("Part 1 · Graph basics", "Part 2 · The idea of the proof",
                      "Part 3 · Lean: three helper lemmas", "Part 4 · Lean: the main proof",
                      "Part 5 · Example vs. proof")

NOT_TOURNAMENT = ("⚠ The graph is NOT a tournament now ({}), so the theorem says nothing "
                  "about it. Press 'Reset to the example' or 'Random tournament'. ")


def _yn(b: bool) -> str:
    return "yes" if b else "no"


def _pair_status(ex, f) -> str:
    u, w = f["u"], f["w"]
    a, b = d_adj(ex.ends, u, w), d_adj(ex.ends, w, u)
    if a != b:
        return (f"the arrow goes {u}→{w}" if a else f"the arrow goes {w}→{u}") + \
            ", exactly one direction ✓"
    return "arrows in BOTH directions ✗" if a else "NO arrow at all ✗"


def _compare(total: int, target: int) -> str:
    return "=" if total == target else (">" if total > target else "<")


def _loop_status(ex, v: int) -> str:
    """What the picture shows right now at v (loops, and in + out against n − 1)."""
    k = sum(p == (v, v) for p in ex.ends.values())
    tot = in_deg(ex.ends, v) + out_deg(ex.ends, v)
    head = (f"Now v = {v} has {k} loop{'s' * (k != 1)}" if k else
            f"Now v = {v} has no loop")
    return (head + f": in + out = {tot} {_compare(tot, ex.n - 1)} {ex.n - 1} = n − 1.")


def _ledger_sentence(ex) -> str:
    v = ex.selected
    outs = out_nbrs(ex.ends, v, ex.vs)
    ins = in_nbrs(ex.ends, v, ex.vs)
    return (f"out-neighbours {{{', '.join(map(str, outs))}}} (orange) and in-neighbours "
            f"{{{', '.join(map(str, ins))}}} (purple): {len(ins)} + {len(outs)} = "
            f"{in_deg(ex.ends, v) + out_deg(ex.ends, v)}, and n − 1 = {ex.n - 1}")


STEPS: list[dict] = [
    dict(
        part=P1, title="Directed graphs: vertices and arrows", code="defs",
        anchors=["structure DGraph", "ends : E → V × V"], focus="edge",
        math=lambda ex, f: (
            "A directed graph has vertices (the blue circles) and arrows between them, "
            "called directed edges. Each arrow starts at its initial vertex and ends at its "
            "terminal vertex. "
            + (f"Gold: the edge {f['e']} goes from {f['a']} to {f['b']}, so it belongs to the "
               f"ordered pair ({f['a']}, {f['b']}). Order matters: ({f['a']}, {f['b']}) and "
               f"({f['b']}, {f['a']}) are different pairs. 'Next example' shows another arrow."
               if f["e"] else "Right now the graph has no arrows.")),
        lean=("`structure DGraph (V E)` has one field, `ends : E → V × V`, which gives every "
              "edge e an ordered pair `G.ends e = (u, w)`. `V × V` is the type of ordered pairs. "
              "`(G.ends e).1` is the first entry (where the arrow starts) and `(G.ends e).2` "
              "the second (where it ends). In the picture, V = {0, …, n − 1}, and only highlighted "
              "arrows show their names e0, e1, …. The other code lines are explained in later "
              "steps."),
    ),
    dict(
        part=P1, title="In-degree and out-degree", code="defs",
        anchors=["def inDeg", "(G.ends e).2 = v)).card", "def outDeg", "(G.ends e).1 = v)).card"],
        focus="vertex",
        math=lambda ex, f: (
            "The out-degree of a vertex v is the number of arrows that LEAVE v (orange). The "
            "in-degree is the number of arrows that ENTER v (purple). Books write deg⁺(v) for "
            "the out-degree and deg⁻(v) for the in-degree. "
            f"For v = {f['v']}: out-degree {out_deg(ex.ends, f['v'])} "
            f"({fmt_pairs(ex.ends, out_edges(ex.ends, f['v']))}), in-degree "
            f"{in_deg(ex.ends, f['v'])} ({fmt_pairs(ex.ends, in_edges(ex.ends, f['v']))}). "
            "The label 'in · out' next to each vertex shows its two numbers. Click a "
            "vertex, or press 'Next example', to count for another vertex."),
        lean=("`inDeg v` is `(Finset.univ.filter (fun e => (G.ends e).2 = v)).card`. "
              "Read it inside out: `Finset.univ` is the finite set of ALL edges, `filter` keeps "
              "the edges whose second entry is v, and `.card` counts them. `outDeg v` is the "
              "same with the first entry `.1`. `[Fintype E]` says there are finitely many "
              "edges, which is what makes `Finset.univ` possible."),
    ),
    dict(
        part=P1, title="Simple: no loops, no multiple edges", code="defs",
        anchors=["def IsLoop (e : E) : Prop := (G.ends e).1", "def HasMultipleEdges",
                 "def IsSimple"], focus=None,
        math=lambda ex, f: (
            "A loop is an arrow from a vertex to itself. Multiple edges are two different "
            "arrows with the same start AND the same end. A directed graph is simple if it "
            "has neither. Right now: loop? "
            f"{_yn(any(is_loop(ex.ends, e) for e in ex.ends))}; multiple edges? "
            f"{_yn(bool(multiple_edge_pairs(ex.ends)))}; simple? {_yn(is_simple(ex.ends))}. "
            "Try the buttons 'Add loop' or 'Copy arrow' under 'Break a rule at v', "
            "then 'Reset to the example'. (Note: 1→2 and 2→1 are NOT multiple edges; they "
            "point in different directions.)"),
        lean=("`IsLoop e` says the two entries of `G.ends e` are equal. `HasMultipleEdges` says "
              "there are edges `e₁ ≠ e₂` with `G.ends e₁ = G.ends e₂`. `IsSimple` is "
              "`¬ G.HasMultipleEdges ∧ ∀ e : E, ¬ G.IsLoop e`: 'there are no multiple edges, "
              "and no edge is a loop'. In Lean, `∧` means 'and', `¬` means 'not', and `∀ e` "
              "means 'for every edge e'."),
    ),
    dict(
        part=P1, title="Tournaments: exactly one arrow per pair", code="defs",
        anchors=["def DAdj", "def IsTournament", "G.IsSimple ∧ ∀ u w : V, u ≠ w → Xor"],
        focus="pair",
        math=lambda ex, f: (
            "A tournament is a simple directed graph in which every two different vertices "
            "are joined by exactly ONE arrow, pointing one way or the other. Think of a "
            "round-robin contest: every two players meet once, and the arrow points from the "
            f"winner to the loser. Gold: the pair {f['u']}, {f['w']}: {_pair_status(ex, f)}. "
            f"(Pair {f['k'] + 1} of {f['total']}; 'Next example' shows the next pair.)"
            if f["u"] is not None else "With one vertex there are no pairs to check."),
        lean=("`DAdj u w` means 'some edge e has `G.ends e = (u, w)`', i.e. (u, w) is an edge. "
              "`IsTournament` is `G.IsSimple ∧ ∀ u w : V, u ≠ w → Xor (G.DAdj u w) "
              "(G.DAdj w u)`: simple, and for all different u, w exactly one of the two holds. "
              "`Xor A B` means 'exactly one of A, B'. Lean defines it as "
              "`(A ∧ ¬B) ∨ (B ∧ ¬A)`, where `∨` means 'or'. The proof uses this form later."),
    ),
    dict(
        part=P1, title="How to read a Lean theorem", code="main",
        anchors=["theorem supp41", "(G : DGraph V E) (hG : G.IsTournament) (v : V) :",
                 "G.inDeg v + G.outDeg v = Fintype.card V - 1"], focus="vertex",
        math=lambda ex, f: (
            "Lean is a program that checks proofs step by step. A theorem has a name (here "
            "supp41), hypotheses before the last colon (what we may assume: G is a directed "
            "graph, hG says G is a tournament, v is a vertex), and a statement after it (what "
            "must be proved). After `:= by` comes the proof: a list of commands called "
            "tactics. At every moment Lean shows the GOAL, the statement still to be proved. "
            "Each tactic changes the goal until nothing is left. `have name : fact := by …` "
            "first proves a smaller fact and names it for later use."),
        lean=("Words you will meet: `Type` = a collection of things (V = the vertices); `Prop` "
              "= a statement, true or false; `ℕ` = the numbers 0, 1, 2, …; `Finset` = a finite "
              "set; `.card` = its number of elements; `namespace` = a folder for names "
              "(GraphCh10, DGraph). `Type*`, `Type u` are technical size labels you can ignore. "
              "Symbols: `∀` for all, `∃` there exists, `∧` and, `∨` or, `¬` not, `→` implies, "
              "`↔` if and only if."),
    ),
    dict(
        part=P1, title="The question, and the answer n − 1", code="main",
        anchors=["theorem supp41", "(G : DGraph V E) (hG : G.IsTournament) (v : V) :",
                 "G.inDeg v + G.outDeg v = Fintype.card V - 1"], focus="ledger",
        math=lambda ex, f: (
            "Question: in a tournament, what is in-degree + out-degree of a vertex v? "
            "Answer: n − 1, where n is the number of vertices. Why: each of the OTHER n − 1 "
            "vertices is joined to v by exactly one arrow. That arrow either enters v (+1 to "
            "the in-degree) or leaves v (+1 to the out-degree). The ledger below the graph "
            f"shows this for v = {ex.selected}: {_ledger_sentence(ex)}."),
        lean=("The theorem is stated for EVERY tournament G with finitely many vertices and "
              "edges, and EVERY vertex v. `hG : G.IsTournament` is the hypothesis 'G is a "
              "tournament'. `Fintype.card V` is n, the number of vertices. `[Fintype V] "
              "[Fintype E]` say there are finitely many vertices and edges. `[DecidableEq V]` "
              "only lets Lean compute with `filter`. Note: on ℕ = {0, 1, 2, …} Lean's subtraction "
              "never goes below 0 (it treats 0 − 1 as 0). That never matters here: v is a "
              "vertex, so n ≥ 1 and n − 1 is the usual value."),
    ),
    dict(
        part=P1, title="Try it: reverse arrows, change n", code="header",
        anchors=["Paper proof."], focus="ledger",
        math=lambda ex, f: (
            "Click an arrow to reverse it. Use 'n − / +' or 'Random tournament' to get other "
            "tournaments. Each time, the ledger shows in + out = n − 1 for the chosen vertex. "
            "Reversing an arrow at v moves 1 from 'in' to 'out' (or back), so the total "
            f"stays the same. Right now, v = {ex.selected}: {_ledger_sentence(ex)}. "
            "Trying examples is not a proof: the Lean proof covers every tournament at once."),
        lean=("Nothing in this step is Lean. The numbers are recomputed from the arrows using "
              "the definitions `inDeg`, `outDeg` and `IsTournament`. The highlighted line starts "
              "the comment at the top of Supp41.lean, the paper proof that the "
              "Lean proof follows. Part 2 explains it."),
    ),
    dict(
        part=P2, title="The plan: three ideas", code="header",
        ranges=[("1. G has no multiple directed edges", "deg⁻(v) + deg⁺(v) = n − 1.")],
        focus="ledger",
        math=lambda ex, f: (
            "In the file comment, deg⁺ means out-degree, deg⁻ means in-degree, and # means "
            "'the number of'. Idea 1, no multiple edges: the arrows leaving v match "
            "one-to-one with the vertices "
            "they point to, so out-degree = number of out-neighbours. In the same way, "
            "in-degree = number of in-neighbours. Idea 2, no loops: v is never its own "
            "neighbour, so all neighbours are among the other n − 1 vertices. "
            "Idea 3, exactly one arrow per pair: each other vertex is an in-neighbour or an "
            "out-neighbour, never both and never neither. So the two counts split the n − 1 "
            "other vertices, and add up to n − 1. The ledger shows the split for v = "
            f"{ex.selected}."),
        lean=("This is the comment at the top of Supp41.lean. The Lean file proves ideas 1 "
              "and 2 as three helper lemmas A, B, C, which use one general fact from Lemmas.lean "
              "(Part 3). The main theorem then combines them with idea 3 (Part 4). A 'neighbour' here is a vertex w with (v, w) an "
              "edge (out-neighbour) or (w, v) an edge (in-neighbour)."),
    ),
    dict(
        part=P3, title="Tactic cheat sheet (come back to it)", code="lemmas",
        anchors=["theorem ends_injective_of_isSimple"], focus="vertex",
        math=lambda ex, f: (
            "You do not need to memorise tactics: 'What it means' always gives the idea, and "
            "'In Lean' shows how each line carries it out. Press ◀ Previous to come back here "
            "whenever a tactic name is unfamiliar."),
        lean=("• `intro x` / `rintro ⟨a, b⟩`: take x, or assume A in 'if A then B' (rintro also "
              "unpacks it)\n"
              "• `exact t`: t proves the goal, done        • `apply f`: use f; then prove what "
              "f needs\n"
              "• `rw [h]`: replace the left side of equation h by its right side\n"
              "• `simp only [rules]`: simplify using exactly these rules\n"
              "• `ext x`: sets are equal if they have the same elements x\n"
              "• `congr 1`: to show f a = f b, show a = b    • `constructor`: split ↔ into two "
              "directions\n"
              "• `refine ⟨?_, h⟩`: give part of the proof now, fill the hole ?_ later\n"
              "• `obtain` / `rcases h with …`: unpack h ('and' → both parts, 'or' → one case "
              "each)\n"
              "• `by_contra h`: assume the opposite, then prove False\n"
              "• `absurd h hn`: h and its negation hn contradict each other   • `calc`: a chain "
              "a = b = c"),
    ),
    dict(
        part=P3, title="Notation cheat sheet (come back to it)", code="out",
        anchors=["have hinj"], focus="vertex",
        math=lambda ex, f: (
            "Besides tactics, Lean proofs use a few pieces of notation. Like the tactic "
            "cheat sheet, this page is for reference: press ◀ Previous to come back."),
        lean=("• ⟨a, b⟩: bundle two parts into one (a proof of 'A and B', or 'there is an e "
              "with …'); after rintro / obtain it UNPACKS them and names the parts\n"
              "• rcases h with ⟨…⟩ | ⟨…⟩: the bar | separates the two cases of an 'or'\n"
              "• h.1, h.2: the first / second part of an 'and' (also first / second entry of "
              "a pair)\n"
              "• h.symm: turn a = b into b = a      • h₁.trans h₂: from a = b and b = c get "
              "a = c\n"
              "• s.image f: the set of all f x for x in s      • x ↦ y: 'x is sent to y'\n"
              "• Function.Injective f: f never sends two different inputs to the same output; "
              "Set.InjOn f s: the same, but only for inputs in s\n"
              "• fun e => …: the function sending e to …      • := names or defines a thing"),
    ),
    dict(
        part=P3, title="A fact used below: different edges, different pairs", code="lemmas",
        ranges=[("theorem ends_injective_of_isSimple", "exact hG.1 ⟨e₁, e₂, hne, hends⟩")],
        focus="vertex",
        math=lambda ex, f: (
            "In a simple directed graph, two DIFFERENT edges always have different ordered "
            "pairs. This is the 'no multiple edges' rule read backwards: if two different "
            "edges had the same pair, they would be multiple edges. So in a simple graph an "
            "arrow is completely described by its pair, like 1→3."),
        lean=("`Function.Injective G.ends` means `G.ends e₁ = G.ends e₂ → e₁ = e₂` (one-to-one). "
              "`intro e₁ e₂ hends` takes two edges and `hends : G.ends e₁ = G.ends e₂`. "
              "`by_contra hne` assumes the opposite, `hne : ¬ e₁ = e₂`, and the goal becomes "
              "`False`. `hG.1` is the first half of `IsSimple`: `¬ G.HasMultipleEdges`. "
              "`⟨e₁, e₂, hne, hends⟩` is a proof of `HasMultipleEdges`, so `hG.1 ⟨…⟩` proves "
              "`False`. This lemma lives in GraphCh10/Lemmas.lean."),
    ),
    dict(
        part=P3, title="Helper A: out-degree = number of out-neighbours", code="out",
        anchors=["theorem outDeg_eq_card_outNbrs", "G.outDeg v = (Finset.univ.filter",
                 "let leaving"], focus="leaving",
        math=lambda ex, f: (
            "Helper lemma A: in a simple directed graph, the out-degree of v equals the "
            "number of out-neighbours of v, the vertices w with (v, w) an edge. These count "
            "different things: arrows versus vertices. "
            f"For v = {f['v']}: the orange arrows leaving v are "
            f"{fmt_pairs(ex.ends, out_edges(ex.ends, f['v']))}, and the out-neighbours (gold) "
            f"are {{{', '.join(map(str, out_nbrs(ex.ends, f['v'], ex.vs)))}}}. "
            "The next three steps show why the two numbers are always equal."),
        lean=("The lemma states `G.outDeg v = (Finset.univ.filter (fun w : V => G.DAdj v w))"
              ".card`: the number of vertices w with `DAdj v w`. `let leaving := …` names the "
              "set of edges whose first entry is v. By definition, `outDeg v` is the size of "
              "`leaving`. The plan is to show that 'take the end vertex', "
              "`fun e => (G.ends e).2`, matches `leaving` one-to-one with the out-neighbours. "
              "`hS` is this lemma's own name for 'G is simple'; Lemmas.lean calls it `hG` and "
              "the main proof `hSimple`. Such names are local labels."),
    ),
    dict(
        part=P3, title="himage: where the leaving arrows point", code="out",
        ranges=[("have himage", "exact ⟨e, by rw [he], by rw [he]⟩")], focus="leaving_edge",
        math=lambda ex, f: (
            "Send each arrow leaving v to the vertex it points to. "
            + (f"Gold: {f['e']} = ({f['v']}, {f['w']}) is sent to {f['w']}. "
               f"(Arrow {f['k'] + 1} of {f['total']}; 'Next example' shows the next one.) "
               if f["e"] else f"Vertex {f['v']} has no leaving arrows right now. ")
            + "The vertices reached this way are exactly the out-neighbours of v: w is reached "
              "exactly when some edge has the pair (v, w), and that is what '(v, w) is an "
              "edge' means."),
        lean=("In short: for each vertex w, Lean checks that 'w is the end of an arrow "
              "leaving v' and '(v, w) is an edge' say the same thing. Details: "
              "`ext w` turns 'two finite sets are equal' into 'w is in one iff w is in the "
              "other' (`↔` = 'if and only if'). `simp only […]` unfolds the memberships. The "
              "goal becomes `(∃ a, (G.ends a).1 = v ∧ (G.ends a).2 = w) ↔ G.DAdj v w`. "
              "`unfold DGraph.DAdj` turns the right side into `∃ e, G.ends e = (v, w)`. "
              "`constructor` splits `↔` into two directions. `Prod.ext he1 he2` builds "
              "`G.ends e = (v, w)` from equal first and second entries. In the other direction, "
              "`rw [he]` reduces both entries to v and w."),
    ),
    dict(
        part=P3, title="hinj: no two leaving arrows hit the same vertex", code="out",
        ranges=[("have hinj", "exact Prod.ext (h₁.trans h₂.symm) hsnd")], focus="leaving",
        math=lambda ex, f: (
            "Two arrows leaving v that point to the same w would both have the pair (v, w). "
            "They would be multiple edges, which a simple graph does not have. This is where "
            "'no multiple edges' is used. See it fail: press 'Copy arrow' at v. The "
            "out-degree goes up by 1, but the number of out-neighbours does not. "
            f"Now for v = {f['v']}: out-degree {out_deg(ex.ends, f['v'])}, out-neighbours "
            f"{len(out_nbrs(ex.ends, f['v'], ex.vs))}."),
        lean=("In short: Lean takes two leaving arrows with the same end vertex and shows "
              "they are the same arrow, using the fact from Lemmas.lean. Details: "
              "`Set.InjOn f s` means f is one-to-one on the set s. `intro e₁ h₁ e₂ h₂ hsnd` "
              "takes two edges in `leaving` (`h₁`, `h₂`) with the same end vertex (`hsnd`). "
              "`simp only … at h₁ h₂` turns `h₁` into `(G.ends e₁).1 = v`. "
              "`apply G.ends_injective_of_isSimple hS` (the fact from Lemmas.lean) changes the "
              "goal to `G.ends e₁ = G.ends e₂`. `Prod.ext` proves it: the first entries are both "
              "v (`h₁.trans h₂.symm`), and the second entries are equal by `hsnd`."),
    ),
    dict(
        part=P3, title="calc: count the arrows by counting where they point", code="out",
        ranges=[("calc G.outDeg v = leaving.card := rfl", "_ = (Finset.univ.filter")],
        focus="leaving",
        math=lambda ex, f: (
            "The matching 'arrow ↦ the vertex it points to' is one-to-one (hinj) and hits "
            "exactly the out-neighbours (himage). So counting the arrows leaving v gives the "
            "same number as counting the out-neighbours. "
            f"For v = {f['v']}: {out_deg(ex.ends, f['v'])} arrows, "
            f"{len(out_nbrs(ex.ends, f['v'], ex.vs))} out-neighbours. This proves helper A."),
        lean=("`calc` proves an equation as a chain of steps `a = b`, `_ = c`, …. "
              "`G.outDeg v = leaving.card := rfl` holds by the definition of `outDeg` (`rfl`: "
              "both sides are the same by definition). `Finset.card_image_of_injOn hinj` says "
              "a one-to-one map does not change the size: `(leaving.image f).card = "
              "leaving.card`. `.symm` turns it around. `rw [himage]` replaces the image by the "
              "set of out-neighbours."),
    ),
    dict(
        part=P3, title="Helper B: in-degree = number of in-neighbours", code="in",
        anchors=["theorem inDeg_eq_card_inNbrs", "let entering", "have himage", "have hinj",
                 "calc G.inDeg v = entering.card := rfl"], focus="entering",
        math=lambda ex, f: (
            "Helper lemma B is the mirror image of helper A: the in-degree of v equals the "
            "number of in-neighbours, the vertices w with (w, v) an edge. Send each arrow "
            "entering v to the vertex it STARTS from. "
            f"For v = {f['v']}: purple arrows {fmt_pairs(ex.ends, in_edges(ex.ends, f['v']))}; "
            f"in-neighbours (gold) {{{', '.join(map(str, in_nbrs(ex.ends, f['v'], ex.vs)))}}}."),
        lean=("The proof repeats helper A with `.1` and `.2` swapped. `entering` is the set of "
              "edges whose second entry is v. The matching is `fun e => (G.ends e).1`. Then "
              "`himage`, `hinj` and `calc` play the same roles as before."),
    ),
    dict(
        part=P3, title="Helper C: v is not its own neighbour", code="loop",
        ranges=[("theorem not_dAdj_self", "exact hS.2 e")], focus="vertex",
        math=lambda ex, f: (
            "Helper lemma C: in a simple directed graph, (v, v) is never an edge, because such "
            "an edge would be a loop. So v is neither its own out-neighbour nor its own "
            "in-neighbour. See it fail: press 'Add loop' at v. A loop adds 1 to the "
            "in-degree AND 1 to the out-degree. " + _loop_status(ex, f['v'])),
        lean=("`¬ G.DAdj v v` means `G.DAdj v v → False`. `rintro ⟨e, he⟩` takes the edge e "
              "that `DAdj` promises, with `he : G.ends e = (v, v)`. `hS.2 e` (second half of "
              "`IsSimple`) says `¬ G.IsLoop e`. `by rw [DGraph.IsLoop, he]` proves "
              "`G.IsLoop e`: unfolding `IsLoop` gives `(G.ends e).1 = (G.ends e).2`, and "
              "rewriting with `he` gives `(v, v).1 = (v, v).2`, i.e. `v = v`, which `rw` "
              "closes by itself. Applying `hS.2 e` to it gives `False`."),
    ),
    dict(
        part=P4, title="obtain: unpack 'G is a tournament'", code="main",
        anchors=["obtain ⟨hSimple, hExactlyOne⟩ := hG", "-- a tournament is simple"],
        focus="vertex",
        math=lambda ex, f: (
            "Now the main proof. Take any tournament G and any vertex v (in the picture, "
            f"v = {f['v']}). 'G is a tournament' contains two facts: G is simple, and every "
            "two different vertices have exactly one arrow between them. We give each "
            "fact its own name so we can use them separately. (The code comments "
            "'(step 1)', '(steps 1 and 3)' below refer to ideas 1–3 of the plan in Part 2, "
            "not to the pages of this walkthrough.)"),
        lean=("`obtain ⟨hSimple, hExactlyOne⟩ := hG` splits the `∧` in `IsTournament`. Now "
              "`hSimple : G.IsSimple` and `hExactlyOne : ∀ u w, u ≠ w → Xor (G.DAdj u w) "
              "(G.DAdj w u)`. The goal is still `G.inDeg v + G.outDeg v = Fintype.card V - 1`."),
    ),
    dict(
        part=P4, title="let others: every vertex except v", code="main",
        anchors=["let others : Finset V := Finset.univ.erase v", "-- the vertices other than `v`"],
        focus="others",
        math=lambda ex, f: (
            "Let 'others' be the set of all vertices except v. It has n − 1 elements. "
            f"In the picture, the {ex.n - 1} others carry the tag 'other'; v = {f['v']} keeps "
            "its tag 'v' and is not one of them."),
        lean=("`Finset.univ` is the finite set of all vertices, and `.erase v` removes v from "
              "it. `let others : Finset V := …` gives this set a name. (`Finset V` means a "
              "finite set of vertices.)"),
    ),
    dict(
        part=P4, title="hOut: out-degree = out-neighbours among the others", code="main",
        ranges=[("have hOut", "exact fun h => h.2")], focus="other_out",
        math=lambda ex, f: (
            "Claim: the out-degree of v = the number of OTHER vertices w with (v, w) an "
            "edge. Helper A says it is the number of ALL vertices w with (v, w) an edge. v "
            "itself is never one of them (helper C, no loops), so leaving v out changes "
            "nothing. "
            + (f"Example w = {f['w']}: is ({f['v']}, {f['w']}) an edge? "
               f"{_yn(d_adj(ex.ends, f['v'], f['w']))}, so w is "
               f"{'' if d_adj(ex.ends, f['v'], f['w']) else 'NOT '}counted. "
               "('Next example' moves w.)" if f["w"] is not None else "")),
        lean=("In short: Lean shows that 'all w with v→w' and 'the others w with v→w' have "
              "the same members. Details: `rw [outDeg_eq_card_outNbrs G hSimple v]` uses "
              "helper A. `congr 1`: two sizes "
              "are equal if the two sets are equal. After `ext w` and `simp only […]`, the goal "
              "is `G.DAdj v w ↔ w ≠ v ∧ G.DAdj v w`. (→) Given `hvw`, `refine ⟨?_, hvw⟩` "
              "leaves `w ≠ v`. `rintro rfl` supposes w = v, and then helper C "
              "(`not_dAdj_self`) contradicts `hvw`. (←) `fun h => h.2` keeps the second part."),
    ),
    dict(
        part=P4, title="hIn: in-neighbours = the others that are not out-neighbours",
        code="main", ranges=[("have hIn", "· exact absurd hvw hnvw")], focus="other_in",
        math=lambda ex, f: (
            "Claim: the in-degree of v = the number of OTHER vertices w with (v, w) NOT an "
            "edge. Helper B says the in-degree counts the w with (w, v) an edge. For w ≠ v, "
            "exactly one of (v, w), (w, v) is an edge (idea 3 of the plan), so '(w, v) is an edge' means "
            "the same as '(v, w) is not an edge'. "
            + (f"Example w = {f['w']}: {f['branch']} ('Next example' moves w.)"
               if f["w"] is not None else "")),
        lean=("In short: for each w, Lean shows '(w, v) is an edge' ⇔ 'w ≠ v and (v, w) is "
              "not an edge', by checking both cases of the Xor. Details: after `rw`, `congr 1`, "
              "`ext w` and `simp only`, the goal is "
              "`G.DAdj w v ↔ w ≠ v ∧ ¬G.DAdj v w`. `rcases hExactlyOne w v hne with … | …` "
              "splits the `Xor` into its two cases: `DAdj w v ∧ ¬DAdj v w`, or "
              "`DAdj v w ∧ ¬DAdj w v`. Lean must handle both cases. In the impossible case, "
              "`absurd` gets a contradiction from a fact and its negation (e.g. `hwv` and "
              "`hnwv`). In the (→) direction, `w ≠ v` again comes from helper C."),
    ),
    dict(
        part=P4, title="calc: the two groups fill the n − 1 others  ∎", code="main",
        ranges=[("calc G.inDeg v + G.outDeg v", "rw [Finset.card_erase_of_mem")],
        focus="ledger",
        math=lambda ex, f: (
            "Every other vertex w is in exactly one of two groups: (v, w) is an edge "
            "(counted by the out-degree, orange) or it is not (counted by the in-degree, "
            "purple). Two groups that split a set have sizes adding up to the size of the "
            "set, here n − 1. So in-degree + out-degree = n − 1. ∎  "
            f"For v = {ex.selected}: {_ledger_sentence(ex)}."),
        lean=("`rw [hIn, hOut, Nat.add_comm]` replaces both degrees by the two group sizes and "
              "swaps their order. `Finset.card_filter_add_card_filter_not` is the library fact "
              "'#(those with p) + #(those without p) = #all'. `Finset.card_erase_of_mem "
              "(Finset.mem_univ v)` says removing v (which is in `univ`) lowers the size by 1. "
              "`Finset.card_univ` says `univ` has `Fintype.card V` elements. The goal becomes "
              "`Fintype.card V - 1 = Fintype.card V - 1`, which `rw` closes."),
    ),
    dict(
        part=P5, title="A picture checks examples; Lean proves it for all", code="main",
        anchors=[], focus="ledger",
        math=lambda ex, f: (
            "Every picture here is ONE tournament. The script also checked every tournament "
            f"with 1 to 6 vertices ({ex.stats['n_tour']:,} graphs). That is evidence, not a "
            "proof: it says nothing about 7 or 1000 vertices. The Lean proof covers every "
            "finite tournament and every vertex, because each step is a general argument. "
            "The 'Break a rule' buttons show that each rule is needed. With a loop, a "
            "copied arrow, arrows both ways, or a missing arrow, in + out can differ from "
            "n − 1."),
        lean=("`#print axioms GraphCh10.supp41` lists only Lean's three standard axioms "
              "(propext, Classical.choice, Quot.sound), basic logical principles that almost every "
              "Lean proof relies on. There is no `sorry` (an unfinished step) and no axiom "
              "added by this project. "
              "Lean's kernel has checked every step shown above."),
    ),
]


# ---------------------------------------------------------------------------
# 8. The interactive explorer
# ---------------------------------------------------------------------------

class Explorer:
    """Interactive companion: inspect degrees, reverse arrows, step through the proof."""

    def __init__(self, stats: dict):
        self.stats = stats
        self.lean = read_lean_sources()
        self._check_anchors()
        self.n = EXAMPLE_N
        self.ends: Ends = dict(EXAMPLE_ENDS)
        self.selected = EXAMPLE_START_V
        self.step = 0
        self.example_idx = 0
        self.seed = 0
        self.message = ""

        for key in ("keymap.back", "keymap.forward"):  # free ← / → for the walkthrough
            plt.rcParams[key] = [k for k in plt.rcParams[key] if k not in ("left", "right")]

        self.fig = plt.figure(figsize=(18, 11.5), facecolor="white")
        try:
            self.fig.canvas.manager.set_window_title("Supp. 41: in-degree + out-degree")
        except AttributeError:
            pass
        self.fig.text(0.015, 0.972,
                      "Supplementary Exercise 41:  in-degree + out-degree in a tournament",
                      fontsize=18, fontweight="bold", color=COLOR_TEXT, va="center")
        self.fig.text(0.015, 0.94,
                      "An interactive companion to the Lean proof GraphCh10.supp41. Every "
                      "picture is one example; the Lean proof covers every tournament.",
                      fontsize=10.5, color=COLOR_WARN, style="italic", va="center")

        self.ax_graph = self.fig.add_axes([0.015, 0.36, 0.465, 0.475])
        self.caption = self.fig.text(0.2475, 0.872, "", ha="center", va="top", fontsize=10.5,
                                     color=COLOR_TEXT, linespacing=1.5)
        self.ax_legend = self.fig.add_axes([0.015, 0.29, 0.465, 0.07])
        self.ax_edit = self.fig.add_axes([0.015, 0.03, 0.165, 0.245])
        self.ax_sets = self.fig.add_axes([0.19, 0.03, 0.29, 0.245])
        self.ax_text = self.fig.add_axes([0.505, 0.615, 0.48, 0.305])
        self.ax_code = self.fig.add_axes([0.505, 0.105, 0.48, 0.5])
        for ax in (self.ax_legend, self.ax_edit, self.ax_sets, self.ax_text, self.ax_code):
            ax.axis("off")
        self.fig.text(0.015, 0.905,
                      "Click a vertex to choose v.   Click an arrow to reverse it.   "
                      "Gold marks what the current step is about.",
                      fontsize=9.8, color="#444444", va="center")

        def button(rect, label, cb, color="#F0F0F0", size=10.5):
            b = Button(self.fig.add_axes(rect), label, color=color, hovercolor="#DDE8F5")
            b.label.set_fontsize(size)
            b.on_clicked(cb)
            return b

        # Tournament controls.
        self.ax_edit.text(0.0, 1.0, "Change the tournament", transform=self.ax_edit.transAxes,
                          fontsize=10.5, fontweight="bold", va="top")
        self.n_label = self.fig.text(0.017, 0.2325, "", fontsize=10, va="center")
        self.btn_n_minus = button([0.095, 0.215, 0.035, 0.035], "n −",
                                  lambda _e: self.set_n(self.n - 1), size=9.5)
        self.btn_n_plus = button([0.135, 0.215, 0.035, 0.035], "n +",
                                 lambda _e: self.set_n(self.n + 1), size=9.5)
        self.btn_random = button([0.017, 0.173, 0.153, 0.035], "Random tournament",
                                 lambda _e: self.randomize(), size=9.5)
        self.btn_reset = button([0.017, 0.131, 0.153, 0.035], "Reset to the example",
                                lambda _e: self.reset(), color="#E3EEDF", size=9.5)
        self.break_label = self.fig.text(0.017, 0.1225, "", fontsize=9.5, va="center",
                                         fontweight="bold", color=COLOR_WARN)
        self.btn_loop = button([0.017, 0.08, 0.0745, 0.035], "Add loop",
                               lambda _e: self.break_rule("loop"), color="#F7E6E6", size=9)
        self.btn_copy = button([0.0955, 0.08, 0.0745, 0.035], "Copy arrow",
                               lambda _e: self.break_rule("copy"), color="#F7E6E6", size=9)
        self.btn_reverse = button([0.017, 0.038, 0.0745, 0.035], "Add reverse",
                                  lambda _e: self.break_rule("reverse"), color="#F7E6E6", size=9)
        self.btn_delete = button([0.0955, 0.038, 0.0745, 0.035], "Delete arrow",
                                 lambda _e: self.break_rule("delete"), color="#F7E6E6", size=9)

        self.btn_prev = button([0.505, 0.035, 0.085, 0.055], "◀ Previous", lambda _e: self.go(-1))
        self.btn_next = button([0.700, 0.035, 0.085, 0.055], "Next ▶", lambda _e: self.go(+1),
                               color="#E3EEDF")
        self.btn_example = button([0.795, 0.035, 0.09, 0.055], "Next example",
                                  lambda _e: self.next_example())
        self.step_label = self.fig.text(0.6425, 0.0625, "", ha="center", va="center",
                                        fontsize=11, fontweight="bold", color=COLOR_TEXT)

        self._draw_legend()
        self.fig.canvas.mpl_connect("button_press_event", self._on_click)
        self.fig.canvas.mpl_connect("key_press_event", self._on_key)
        self.enter_step(0)

    # -- state --------------------------------------------------------------

    def _check_anchors(self) -> None:
        """Every walkthrough anchor / range end must match exactly one line of its source."""
        for s in STEPS:
            lines = self.lean[s["code"]]
            subs = list(s.get("anchors", [])) + [x for r in s.get("ranges", []) for x in r]
            for sub in subs:
                n = sum(sub in ln for ln in lines)
                assert n == 1, f"anchor {sub!r} matches {n} lines of the {s['code']} source"

    def highlighted(self, s: dict) -> list[int]:
        """Indices of the source lines a step highlights."""
        lines = self.lean[s["code"]]
        idx = {i for a in s.get("anchors", []) for i, ln in enumerate(lines) if a in ln}
        for a, b in s.get("ranges", []):
            i = next(i for i, ln in enumerate(lines) if a in ln)
            j = next(j for j, ln in enumerate(lines) if b in ln)
            assert i <= j
            idx |= set(range(i, j + 1))
        return sorted(idx)

    @property
    def vs(self) -> list[int]:
        return list(range(self.n))

    @property
    def tournament(self) -> bool:
        return is_tournament(self.ends, self.vs)

    @property
    def is_example(self) -> bool:
        return self.n == EXAMPLE_N and self.ends == EXAMPLE_ENDS

    def _new_graph(self, n: int, ends: Ends, msg: str = "") -> None:
        self.n, self.ends, self.message = n, ends, msg
        if self.selected >= n:
            self.selected = 0
        self.example_idx = 0
        self.redraw()

    def set_n(self, n: int) -> None:
        if 2 <= n <= 7 and n != self.n:
            self.seed += 1
            rng = random.Random(1000 * n + self.seed)
            bits = [rng.randint(0, 1) for _ in range(n * (n - 1) // 2)]
            self._new_graph(n, tournament_from_bits(n, bits), f"a new tournament with {n} vertices")

    def randomize(self) -> None:
        self.seed += 1
        rng = random.Random(1000 * self.n + self.seed)
        bits = [rng.randint(0, 1) for _ in range(self.n * (self.n - 1) // 2)]
        self._new_graph(self.n, tournament_from_bits(self.n, bits), "a random tournament")

    def reset(self) -> None:
        self.selected = EXAMPLE_START_V
        self._new_graph(EXAMPLE_N, dict(EXAMPLE_ENDS))

    def flip(self, e: str) -> None:
        u, w = self.ends[e]
        if u != w:
            self.ends = {**self.ends, e: (w, u)}
            self.message = f"reversed {e}: now {w}→{u}"
            self.redraw()

    def _fresh_name(self) -> str:
        k = 0
        while f"e{k}" in self.ends:
            k += 1
        return f"e{k}"

    def break_rule(self, kind: str) -> None:
        """Break one rule of 'tournament' at the chosen vertex v."""
        v, ends = self.selected, dict(self.ends)
        at_v = [e for e, (a, b) in ends.items() if v in (a, b) and a != b]
        if kind == "loop":
            ends[self._fresh_name()] = (v, v)
            msg = f"added a loop at {v}"
        elif kind == "copy" and at_v:
            leaving = [e for e in at_v if ends[e][0] == v]
            src = (leaving or at_v)[0]  # prefer an arrow leaving v (used by step 'hinj')
            ends[self._fresh_name()] = ends[src]
            k = sum(q == ends[src] for q in ends.values())
            msg = f"added a copy of {ends[src][0]}→{ends[src][1]} (now {k} copies)"
        elif kind == "reverse":
            single = [e for e in at_v if not d_adj(ends, ends[e][1], ends[e][0])]
            if not single:
                return
            a, b = ends[single[0]]
            ends[self._fresh_name()] = (b, a)
            msg = f"added {b}→{a}: arrows both ways between {a} and {b}"
        elif kind == "delete" and at_v:
            a, b = ends.pop(at_v[0])
            msg = f"deleted {a}→{b}"
        else:
            return
        self.ends, self.message = ends, msg
        self.redraw()

    def go(self, delta: int) -> None:
        self.enter_step(max(0, min(len(STEPS) - 1, self.step + delta)))

    def next_example(self) -> None:
        """Next arrow / pair / w for steps that walk through items; else the next vertex."""
        kind = STEPS[self.step]["focus"]
        if kind in ("edge", "pair", "leaving_edge", "other_out", "other_in"):
            self.example_idx += 1
        else:
            self.selected = (self.selected + 1) % self.n
        self.redraw()

    def enter_step(self, k: int) -> None:
        self.step, self.example_idx = k, 0
        self.redraw()

    # -- events -------------------------------------------------------------

    def _on_click(self, event) -> None:
        if event.inaxes is not self.ax_graph or event.button != 1 or event.xdata is None:
            return
        x, y = event.xdata, event.ydata
        pos = positions(self.n)
        v = min(self.vs, key=lambda w: (pos[w][0] - x) ** 2 + (pos[w][1] - y) ** 2)
        if (pos[v][0] - x) ** 2 + (pos[v][1] - y) ** 2 <= (1.5 * NODE_R) ** 2:
            self.select_vertex(v)
            return
        best, dist = None, 0.16
        for e, (a, b) in self.ends.items():
            if a == b:
                continue
            d = min(math.hypot(px - x, py - y) for px, py in edge_curve(pos, self.ends, e, 40))
            if d < dist:
                best, dist = e, d
        if best is not None:
            self.flip(best)

    def select_vertex(self, v: int) -> None:
        self.selected, self.example_idx = v, 0
        self.redraw()

    def _on_key(self, event) -> None:
        if event.key == "right":
            self.go(+1)
        elif event.key == "left":
            self.go(-1)

    # -- what to highlight --------------------------------------------------

    def focus_info(self, kind: str | None) -> tuple[dict, int]:
        """What the current step highlights. Returns (info, #examples 'Next example' cycles)."""
        v, ends, vs = self.selected, self.ends, self.vs
        base = dict(v=v, edges=v_colors(ends, v), emph=frozenset(), tags={v: "v"},
                    caption=deg_formula(ends, v, vs))
        if kind in (None, "vertex", "ledger"):
            return base, self.n
        if kind == "edge":
            names = [e for e in ends]
            if not names:
                return dict(base, e=None, edges={}, tags={}, caption="no arrows"), 0
            k = self.example_idx % len(names)
            e = names[k]
            a, b = ends[e]
            tags = {a: "start"} if a == b else {a: "start", b: "end"}
            return dict(base, e=e, a=a, b=b, edges={e: COLOR_FOCUS}, emph=frozenset({e}),
                        tags=tags, caption=f"{e}: G.ends {e} = ({a}, {b})   (arrow {k + 1} of "
                                           f"{len(names)})"), len(names)
        if kind == "pair":
            pairs = list(combinations(vs, 2))
            if not pairs:
                return dict(base, u=None, w=None), 0
            k = self.example_idx % len(pairs)
            u, w = pairs[k]
            between = [e for e, p in ends.items() if set(p) == {u, w} and u != w]
            return dict(base, u=u, w=w, k=k, total=len(pairs),
                        edges={e: COLOR_FOCUS for e in between}, emph=frozenset(between),
                        tags={u: "u", w: "w"},
                        caption=f"pair {u}, {w}:  DAdj {u} {w} = {d_adj(ends, u, w)},  "
                                f"DAdj {w} {u} = {d_adj(ends, w, u)}  →  Xor "
                                f"{'holds ✓' if d_adj(ends, u, w) != d_adj(ends, w, u) else 'FAILS ✗'}"
                        ), len(pairs)
        if kind in ("leaving", "entering"):
            es = out_edges(ends, v) if kind == "leaving" else in_edges(ends, v)
            col = COLOR_OUT if kind == "leaving" else COLOR_IN
            nb = out_nbrs(ends, v, vs) if kind == "leaving" else in_nbrs(ends, v, vs)
            tags = {w: ("out-nbr" if kind == "leaving" else "in-nbr") for w in nb if w != v}
            tags[v] = "v"
            word = "leaving" if kind == "leaving" else "entering"
            return dict(base, edges={e: col for e in es}, emph=frozenset(es), tags=tags,
                        caption=f"{len(es)} arrows {word} {v}: {fmt_pairs(ends, es)}   →   "
                                f"{len(nb)} {'out' if kind == 'leaving' else 'in'}-neighbours "
                                f"{{{', '.join(map(str, nb))}}}"), self.n
        if kind == "leaving_edge":
            es = [e for e in out_edges(ends, v) if ends[e][1] != v]
            if not es:
                return dict(base, e=None, edges={}, caption=f"no arrows leave {v}"), 0
            k = self.example_idx % len(es)
            e = es[k]
            w = ends[e][1]
            return dict(base, e=e, w=w, k=k, total=len(es),
                        edges={**{x: COLOR_OUT for x in es}, e: COLOR_FOCUS},
                        emph=frozenset({e}), tags={v: "v", w: f"{e} ↦ {w}"},
                        caption=f"{e} = ({v}, {w})  ↦  (G.ends {e}).2 = {w}   "
                                f"(arrow {k + 1} of {len(es)})"), len(es)
        if kind == "others":
            return dict(base, edges={}, tags={**{w: "other" for w in vs if w != v}, v: "v"},
                        caption=f"others = all vertices except {v} = "
                                f"{{{', '.join(str(w) for w in vs if w != v)}}}, "
                                f"{self.n - 1} elements"), self.n
        if kind in ("other_out", "other_in"):
            others = [w for w in vs if w != v]
            if not others:
                return dict(base, w=None, branch=""), 0
            k = self.example_idx % len(others)
            w = others[k]
            vw, wv = d_adj(ends, v, w), d_adj(ends, w, v)
            between = [e for e, p in ends.items() if set(p) == {v, w}]
            if kind == "other_out":
                cap = (f"w = {w}:  ({v}, {w}) is an edge? {_yn(vw)}  →  "
                       f"{'counted in hOut' if vw else 'not counted in hOut'}")
                branch = ""
            else:
                if wv and not vw:
                    branch = (f"({w}, {v}) is an edge and ({v}, {w}) is not. This is the first "
                              f"case of the Xor; w is counted as an in-neighbour.")
                elif vw and not wv:
                    branch = (f"({v}, {w}) is an edge and ({w}, {v}) is not. This is the second "
                              f"case of the Xor; w is NOT an in-neighbour.")
                else:
                    branch = "here the Xor fails: the graph is not a tournament."
                cap = (f"w = {w}:  ({w}, {v}) edge? {_yn(wv)};  ({v}, {w}) edge? {_yn(vw)}  →  "
                       f"{'in-neighbour' if wv and not vw else 'not an in-neighbour'}")
            return dict(base, w=w, k=k, branch=branch,
                        edges={**v_colors(ends, v), **{e: COLOR_FOCUS for e in between}},
                        emph=frozenset(between), tags={v: "v", w: "w"},
                        caption=cap + f"   (w {k + 1} of {len(others)})"), len(others)
        raise ValueError(kind)

    # -- drawing ------------------------------------------------------------

    def redraw(self) -> None:
        s = STEPS[self.step]
        focus, n_examples = self.focus_info(s["focus"])
        self._draw_graph(focus)
        self._draw_ledger()
        self._draw_text(s, focus)
        self._draw_code(s)
        last = len(STEPS) - 1
        self.step_label.set_text(f"Page {self.step + 1} / {len(STEPS)}"
                                 + ("  (end)" if self.step == last else ""))
        self.btn_prev.label.set_alpha(0.3 if self.step == 0 else 1.0)
        self.btn_next.label.set_alpha(0.3 if self.step == last else 1.0)
        for b, off, on_color in ((self.btn_prev, self.step == 0, "#F0F0F0"),
                                 (self.btn_next, self.step == last, "#E3EEDF")):
            b.color = "#F7F7F7" if off else on_color
            b.ax.set_facecolor(b.color)
        self.n_label.set_text(f"vertices: n = {self.n}  (2–7)")
        self.break_label.set_text(f"Break a rule at v = {self.selected}:")
        self.btn_example.ax.set_visible(n_examples > 1)
        self.fig.canvas.draw_idle()

    def _draw_graph(self, focus: dict) -> None:
        ax = self.ax_graph
        ax.clear()
        if self.is_example:
            head = "The example tournament (5 vertices)"
        elif self.tournament:
            head = f"A tournament with {self.n} vertices"
        else:
            head = "⚠ NOT a tournament: " + "; ".join(broken_reasons(self.ends, self.vs))
        if self.message:
            head += f"   [{self.message}]"
        draw_graph(ax, self.ends, self.vs, focus["edges"], focus["emph"], focus["tags"],
                   chosen=self.selected)
        frame(ax)
        self.caption.set_text(textwrap.fill(head, 100) + "\n" + textwrap.fill(focus["caption"], 110))

    def _draw_legend(self) -> None:
        handles = [
            Patch(facecolor=COLOR_VERTEX, edgecolor="#2A4F85", label="vertex"),
            Line2D([], [], color=COLOR_OUT, linewidth=3, label="arrow leaving v (out)"),
            Line2D([], [], color=COLOR_IN, linewidth=3, label="arrow entering v (in)"),
            Line2D([], [], color=COLOR_EDGE, linewidth=3, label="other arrow"),
            Line2D([], [], color=COLOR_LOOP, linewidth=3, linestyle="--", label="loop"),
            Patch(facecolor=COLOR_FOCUS, alpha=0.6, label="gold: this step"),
        ]
        self.ax_legend.legend(handles=handles, loc="center", ncol=3, frameon=False,
                              fontsize=9.5, handlelength=2.2, columnspacing=1.4)

    def _draw_ledger(self) -> None:
        """For the chosen v: what each other vertex (and each loop) adds to in + out."""
        ax = self.ax_sets
        ax.clear()
        ax.axis("off")
        ax.add_patch(plt.Rectangle((0, 0), 1, 1, transform=ax.transAxes, facecolor="#F7F7F7",
                                   edgecolor="#D0D0D0"))
        v, ends, vs = self.selected, self.ends, self.vs
        ax.text(0.03, 0.94, f"Ledger for v = {v}: what each other vertex adds to in + out",
                transform=ax.transAxes, fontsize=10.5, fontweight="bold", va="top")
        chips = []
        for w in vs:
            if w == v:
                continue
            o = sum(p == (v, w) for p in ends.values())
            i = sum(p == (w, v) for p in ends.values())
            if (o, i) == (1, 0):
                chips.append((f"w = {w}", f"{v}→{w}", "out +1", COLOR_OUT, "#FDF0E1"))
            elif (o, i) == (0, 1):
                chips.append((f"w = {w}", f"{w}→{v}", "in +1", COLOR_IN, "#EFE6F7"))
            elif o + i == 0:
                chips.append((f"w = {w}", "no arrow", "+0 ✗", COLOR_WARN, "#FBE3E3"))
            else:
                chips.append((f"w = {w}", f"out {o}, in {i}", f"+{o + i} ✗", COLOR_WARN,
                              "#FBE3E3"))
        n_loops = sum(p == (v, v) for p in ends.values())
        if n_loops:
            chips.append((f"loop ×{n_loops}", f"{v}→{v}", f"+{2 * n_loops} ✗", COLOR_WARN,
                          "#FBE3E3"))
        k = max(len(chips), 1)
        cw = min(0.94 / k, 0.2)
        x0 = 0.03
        for j, (top, mid, bot, col, bg) in enumerate(chips):
            x = x0 + j * cw
            ax.add_patch(FancyBboxPatch((x + 0.006, 0.36), cw - 0.012, 0.42,
                                        boxstyle="round,pad=0.005,rounding_size=0.02",
                                        transform=ax.transAxes, facecolor=bg, edgecolor=col,
                                        linewidth=1.6))
            for yy, t, fw, fs in ((0.71, top, "bold", 9.5), (0.57, mid, "normal", 9.5),
                                  (0.43, bot, "bold", 10)):
                ax.text(x + cw / 2, yy, t, transform=ax.transAxes, ha="center", va="center",
                        fontsize=fs if k <= 6 else fs - 1, fontweight=fw,
                        color=col if t is bot else COLOR_TEXT)
        if not chips:
            ax.text(0.5, 0.57, "no other vertices (n = 1)", transform=ax.transAxes,
                    ha="center", fontsize=10)
        i, o = in_deg(ends, v), out_deg(ends, v)
        ok = i + o == self.n - 1
        ax.text(0.03, 0.24, f"in {i} + out {o} = {i + o}     n − 1 = {self.n - 1}     "
                f"{'✓ equal' if ok else '✗ different'}",
                transform=ax.transAxes, fontsize=11, fontweight="bold", va="center",
                color=COLOR_OK if ok else COLOR_WARN, family="DejaVu Sans Mono")
        t = self.tournament
        ax.text(0.03, 0.09, ("tournament ✓  (simple, and exactly one arrow per pair)" if t else
                             "not a tournament ✗  (the theorem does not apply)"),
                transform=ax.transAxes, fontsize=10, fontweight="bold", va="center",
                color=COLOR_OK if t else COLOR_WARN)

    def _draw_text(self, s: dict, focus: dict) -> None:
        ax = self.ax_text
        ax.clear()
        ax.axis("off")
        math_txt = s["math"](self, focus)
        if not self.tournament:
            math_txt = NOT_TOURNAMENT.format("; ".join(broken_reasons(self.ends, self.vs))) \
                + math_txt
        blocks = [("What it means", math_txt.replace("`", "")),
                  ("In Lean", s["lean"].replace("`", ""))]

        # Shrink the font until everything fits the panel.
        height_pt = ax.get_position().height * self.fig.get_figheight() * 72
        for size in (11.5, 11, 10.5, 10, 9.5, 9, 8.5, 8):
            width = int(112 * 10 / size)
            wrapped = [(h, [ln for para in t.split("\n") for ln in textwrap.wrap(para, width)])
                       for h, t in blocks]
            n_lines = 1.3 + 1.9 + sum(1.25 + len(w) + 0.6 for _h, w in wrapped)
            if n_lines * size * 1.42 <= height_pt:
                break
        self.text_fontsize = size
        line = size * 1.42 / height_pt  # one text line, in axes fraction

        y = 1.0
        ax.text(0, y, s["part"].upper(), transform=ax.transAxes, fontsize=size - 0.5,
                color="#777777", va="top", fontweight="bold")
        y -= 1.3 * line
        ax.text(0, y, s["title"], transform=ax.transAxes, fontsize=size + 4, va="top",
                fontweight="bold", color=COLOR_TEXT)
        y -= 1.9 * line
        for head, lines in wrapped:
            ax.text(0, y, head, transform=ax.transAxes, fontsize=size, va="top",
                    fontweight="bold", color=COLOR_OK if head == "In Lean" else COLOR_VERTEX)
            y -= 1.25 * line
            ax.text(0, y, "\n".join(lines), transform=ax.transAxes, fontsize=size, va="top",
                    color=COLOR_TEXT, linespacing=1.42)
            y -= (len(lines) + 0.6) * line

    MAX_CODE_LINES = 32

    def code_window(self, s: dict) -> tuple[int, int]:
        """The slice of the source shown: everything if it fits, else a window that contains
        all highlighted lines (centred on them)."""
        n, hl = len(self.lean[s["code"]]), self.highlighted(s)
        m = self.MAX_CODE_LINES
        if n <= m:
            return 0, n
        if not hl:
            return 0, m
        lo, hi = hl[0], hl[-1] + 1
        assert hi - lo <= m, "highlighted block taller than the code panel"
        start = max(0, min(lo - (m - (hi - lo)) // 2, n - m))
        return start, start + m

    def _draw_code(self, s: dict) -> None:
        ax = self.ax_code
        ax.clear()
        ax.axis("off")
        ax.add_patch(plt.Rectangle((0, 0), 1, 1, transform=ax.transAxes,
                                   facecolor=COLOR_CODE_BG, edgecolor="#D0D0D0"))
        src = self.lean[s["code"]]
        hl = set(self.highlighted(s))
        a, b = self.code_window(s)
        rows = []
        if a > 0:
            rows.append((None, f"   ...  ({a} line{'s' * (a != 1)} above)"))
        rows += [(i, src[i]) for i in range(a, b)]
        if b < len(src):
            rows.append((None, f"   ...  ({len(src) - b} line{'s' * (len(src) - b != 1)} below)"))
        ax.text(0.015, 0.975, f"Lean source: {SOURCE_NAMES[s['code']]}  (read from disk; "
                f"highlighted = this step)", transform=ax.transAxes, fontsize=9.5,
                fontweight="bold", va="top", color="#555555")
        n = max(len(rows), 22)
        step_y = 0.89 / n
        fontsize = 9 if n <= 28 else 8.2
        for r, (i, ln) in enumerate(rows):
            is_hl = i is not None and i in hl
            y = 0.925 - r * step_y
            if is_hl:
                ax.add_patch(plt.Rectangle((0.008, y - step_y * 0.95), 0.984, step_y * 0.98,
                                           transform=ax.transAxes, facecolor=COLOR_CODE_HL,
                                           edgecolor=COLOR_FOCUS, linewidth=1))
            comment = ln.strip().startswith("--") or i is None
            ax.text(0.015, y, ln if ln else " ", transform=ax.transAxes, va="top",
                    fontsize=fontsize, family="DejaVu Sans Mono",
                    color=COLOR_TEXT if is_hl or not comment else "#6A737D",
                    fontweight="bold" if is_hl else "normal")


# ---------------------------------------------------------------------------
# 9. Headless self-test of the explorer (--snapshots)
# ---------------------------------------------------------------------------

def _press(fig, ax, x: float, y: float, data: bool = True) -> None:
    """Simulate a left mouse click at (x, y) in data coordinates (or axes fraction)."""
    fig.canvas.draw()
    tx, ty = (ax.transData if data else ax.transAxes).transform((x, y))
    for name in ("button_press_event", "button_release_event"):
        fig.canvas.callbacks.process(name, MouseEvent(name, fig.canvas, tx, ty, button=1))


def _click(ex: Explorer, btn: Button) -> None:
    _press(ex.fig, btn.ax, 0.5, 0.5, data=False)


def _check_layout(ex: Explorer) -> None:
    """No text in the explanation panel runs past its bottom or right edge."""
    ex.fig.canvas.draw()
    renderer = ex.fig.canvas.get_renderer()
    for ax in (ex.ax_text, ex.ax_code, ex.ax_sets):
        box = ax.get_window_extent(renderer)
        for t in ax.texts:
            if not t.get_text().strip():
                continue
            bb = t.get_window_extent(renderer)
            assert bb.y0 >= box.y0 - 2 and bb.x1 <= box.x1 + 2, \
                f"text overflows its panel: {t.get_text()[:60]!r}"


def self_test(ex: Explorer, outdir: Path) -> None:
    outdir.mkdir(parents=True, exist_ok=True)
    pos = positions(ex.n)
    # 1. Every step renders for every example it offers, and its text and code fit.
    for k, s in enumerate(STEPS):
        ex.enter_step(k)
        _f, n = ex.focus_info(s["focus"])
        for _ in range(max(n, 1)):
            ex.redraw()
            _check_layout(ex)
            ex.next_example()
        ex.reset()
        ex.enter_step(k)
        a, b = ex.code_window(s)
        assert all(a <= i < b for i in ex.highlighted(s)), f"step {k + 1}: highlight off-screen"
        assert ex.highlighted(s) or s["title"].startswith("A picture"), f"step {k + 1}: no code"
        ex.fig.savefig(outdir / f"step_{k + 1:02d}.png", dpi=90)
    # 2. Next / Previous buttons and the arrow keys.
    ex.enter_step(0)
    _click(ex, ex.btn_next)
    assert ex.step == 1, "Next button did not advance"
    _click(ex, ex.btn_prev)
    assert ex.step == 0, "Previous button did not go back"
    _click(ex, ex.btn_prev)
    assert ex.step == 0, "Previous on step 1 must stay on step 1"
    ex.enter_step(len(STEPS) - 1)
    _click(ex, ex.btn_next)
    assert ex.step == len(STEPS) - 1, "Next on the last step must stay there"
    # 3. Clicking a vertex chooses v; the ledger then adds up to n − 1.
    ex.reset()
    ex.enter_step(1)
    for v in ex.vs:
        _press(ex.fig, ex.ax_graph, *pos[v])
        assert ex.selected == v
        f, _n = ex.focus_info("vertex")
        assert set(f["edges"]) == set(out_edges(ex.ends, v)) | set(in_edges(ex.ends, v))
        assert in_deg(ex.ends, v) + out_deg(ex.ends, v) == EXAMPLE_N - 1
    _press(ex.fig, ex.ax_graph, *pos[2])
    ex.fig.savefig(outdir / "click_vertex_2.png", dpi=90)
    # 4. Clicking an arrow reverses it; the graph stays a tournament and the sums stay n − 1.
    ex.reset()
    e = "e6"  # 4→1
    px, py = edge_curve(pos, ex.ends, e)[12]
    _press(ex.fig, ex.ax_graph, px, py)
    assert ex.ends[e] == (1, 4), f"clicking the arrow did not reverse it: {ex.ends[e]}"
    assert ex.tournament and in_deg(ex.ends, 1) == 1 and out_deg(ex.ends, 1) == 3
    assert all(in_deg(ex.ends, v) + out_deg(ex.ends, v) == 4 for v in ex.vs)
    ex.fig.savefig(outdir / "click_arrow_flip.png", dpi=90)
    # ... a click on empty space changes nothing.
    before = dict(ex.ends)
    _press(ex.fig, ex.ax_graph, 3.1, -2.6)
    assert ex.ends == before
    # 5. n − / + and Random keep a tournament, and the formula holds everywhere.
    ex.reset()
    for btn, expect in ((ex.btn_n_plus, 6), (ex.btn_n_plus, 7), (ex.btn_n_plus, 7),
                        (ex.btn_n_minus, 6), (ex.btn_random, 6)):
        _click(ex, btn)
        assert ex.n == expect and ex.tournament
        assert all(in_deg(ex.ends, v) + out_deg(ex.ends, v) == ex.n - 1 for v in ex.vs)
    ex.fig.savefig(outdir / "random_6.png", dpi=90)
    for _ in range(6):
        _click(ex, ex.btn_n_minus)
    assert ex.n == 2 and ex.tournament
    for k in range(len(STEPS)):  # every step renders on the smallest tournament
        ex.enter_step(k)
        _check_layout(ex)
    # 6. Breaking each rule at v makes the graph a non-tournament with in + out ≠ n − 1.
    expected = {"loop": +2, "copy": +1, "reverse": +1, "delete": -1}
    for kind, btn in (("loop", ex.btn_loop), ("copy", ex.btn_copy),
                      ("reverse", ex.btn_reverse), ("delete", ex.btn_delete)):
        ex.reset()
        v = ex.selected
        _click(ex, btn)
        assert not ex.tournament, kind
        assert in_deg(ex.ends, v) + out_deg(ex.ends, v) == EXAMPLE_N - 1 + expected[kind], kind
        for k in range(len(STEPS)):  # every step still renders, with the warning
            ex.enter_step(k)
            _check_layout(ex)
        ex.enter_step(next(i for i, s in enumerate(STEPS)
                           if s["focus"] == ("other_in" if kind == "reverse" else "ledger")))
        ex.fig.savefig(outdir / f"break_{kind}.png", dpi=90)
    # The 'copy' case shows why hinj needs simplicity: out-degree ≠ #out-neighbours.
    ex.reset()
    v = ex.selected
    od, on = out_deg(ex.ends, v), len(out_nbrs(ex.ends, v, ex.vs))
    _click(ex, ex.btn_copy)
    assert out_deg(ex.ends, v) == od + 1 and len(out_nbrs(ex.ends, v, ex.vs)) == on, \
        "Copy arrow must copy an arrow LEAVING v"
    assert out_deg(ex.ends, v) + in_deg(ex.ends, v) == len(out_nbrs(ex.ends, v, ex.vs)) + \
        len(in_nbrs(ex.ends, v, ex.vs)) + 1
    _click(ex, ex.btn_reset)
    assert ex.is_example and ex.tournament and ex.selected == EXAMPLE_START_V
    # 7. The hIn step's case split agrees with the Xor at every w.
    hin = next(i for i, s in enumerate(STEPS) if s["focus"] == "other_in")
    ex.enter_step(hin)
    for _ in range(ex.n - 1):
        f, _n = ex.focus_info("other_in")
        first = d_adj(ex.ends, f["w"], ex.selected)
        assert ("first case" in f["branch"]) == first and ("second case" in f["branch"]) != first
        _click(ex, ex.btn_example)
    print(f"Explorer self-test passed: {len(STEPS)} steps rendered (every example, text and "
          f"code fit), buttons, keys, vertex and arrow clicks, n / random / break / reset "
          f"work; snapshots in {outdir}")


# ---------------------------------------------------------------------------
# 10. Entry point
# ---------------------------------------------------------------------------

def main() -> None:
    try:
        sys.stdout.reconfigure(encoding="utf-8")  # so ≠, ∀ print on Windows consoles
    except (AttributeError, ValueError):
        pass
    parser = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    parser.add_argument("--static", action="store_true",
                        help="only run the checks and save the PNG (no window)")
    parser.add_argument("--snapshots", metavar="DIR", type=Path,
                        help="headless self-test of the explorer; save one PNG per step")
    args = parser.parse_args()

    stats = run_checks()
    vs = list(range(EXAMPLE_N))
    print("Example tournament:", ", ".join(f"{u}→{w}" for u, w in EXAMPLE_ENDS.values()))
    print("in + out:", ", ".join(f"v={v}: {in_deg(EXAMPLE_ENDS, v)}+{out_deg(EXAMPLE_ENDS, v)}"
                                 for v in vs), f"(n − 1 = {EXAMPLE_N - 1})")
    print(f"All assertions passed (approved statement, example, Lean test graphs, "
          f"{stats['n_tour']:,} tournaments on 1..6 vertices, broken-rule examples).")

    out = Path(__file__).resolve().parent / "supp41.png"
    fig = build_figure(stats)
    fig.savefig(out, dpi=150, facecolor="white")
    plt.close(fig)
    print("Saved", out)

    if args.snapshots:
        self_test(Explorer(stats), args.snapshots)
    elif not args.static:
        if matplotlib.get_backend().lower() == "agg":
            print("No interactive Matplotlib backend is available; the explorer needs a "
                  "window (e.g. TkAgg). The PNG has been saved.")
            return
        Explorer(stats)
        print("Opening the interactive explorer (close the window to exit).")
        plt.show()


if __name__ == "__main__":
    main()
