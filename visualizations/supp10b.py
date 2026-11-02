"""Visualization for Rosen Ch. 10, Supplementary Exercise 10(b):  |N(v)| = deg v  ⇔  G is simple.

    "Let G = (V, E) be an undirected graph. Show that |N(v)| = deg v for all v ∈ V if and
     only if G is a simple graph."

An EDUCATIONAL COMPANION to the Lean theorem `GraphCh10.supp10b`
(GraphCh10/Exercises/Supp10b.lean), for students learning Lean 4 and introductory graph
theory. It has two parts:

1. A static summary figure (visualizations/supp10b.png).
2. An interactive explorer: switch between four small example graphs (simple, with a loop,
   with parallel edges, with both), click a vertex to choose v and see its incident edges
   I(v), its loops L(v), its neighbours N(v) and the "other-endpoint map" from I(v) to N(v);
   add or remove a loop or a parallel edge at v and watch |N(v)| = deg v break and come
   back; and step through the actual Lean proof with Previous/Next. Each step separates the
   graph-theory idea from the Lean syntax and highlights the matching Lean lines, which are
   read from the project files at runtime.

The key picture: a loop at v adds 2 to deg v but at most one neighbour (v itself); a second
parallel edge adds 1 to deg v but no new neighbour. Every such "wasted" unit of degree is
visible as the gap deg v − |N(v)|.

Every picture shows ONE graph and only illustrates the statement. The script also checks
every graph with at most 4 vertices and at most 4 edges (loops and multiple edges allowed),
which is still evidence, not a proof. The general statement, for every finite undirected
graph, is established by the Lean proof.

The graph model follows GraphCh10/Definitions.lean and Supp10b.lean exactly:

* `UGraph V E` -- vertices V, edges E, and `ends : E → Sym2 V`, the set {u, w} (one or two
  elements) associated to each edge. Here `ends[e]` is a frozenset of size 1 (a loop) or 2.
  Distinct edges may have equal ends (multiple edges).
* `IsLoop e := (G.ends e).IsDiag`                     -- `is_loop`: ends e has one element.
* `Adj u w := ∃ e, G.ends e = s(u, w)`                -- `adj`; a loop makes v adjacent to v.
* `Incident e v := v ∈ G.ends e`                      -- `incident`.
* `deg v := #{e | Incident e v} + #{e | ends e = s(v, v)}`  -- `deg`: loops counted twice.
* `nbrFinset v := univ.filter (Adj v ·)`              -- `nbr_finset`: N(v) as a finite set.
* `HasMultipleEdges := ∃ e₁ e₂, e₁ ≠ e₂ ∧ ends e₁ = ends e₂`;
  `IsSimple := ¬ HasMultipleEdges ∧ ∀ e, ¬ IsLoop e`.
* From Supp10b.lean: `incidentEdges v` = I(v), `loopsAt v` = L(v), and `otherEnd v e`, the
  other endpoint of e at v (v itself for a loop) -- `incident_edges`, `loops_at`, `other_end`.

Every number is COMPUTED from `ends` with these definitions; none is hardcoded.

Run (from the project root):
    python -m pip install networkx matplotlib
    python visualizations/supp10b.py              # save the PNG, then open the explorer
    python visualizations/supp10b.py --static     # only checks + PNG (no window)
    python visualizations/supp10b.py --snapshots DIR
        # headless self-test: drives the explorer through every walkthrough step,
        # simulates mouse clicks and button presses, and saves PNGs into DIR

Explorer controls:
    click a vertex              choose the vertex v (its edges, neighbours and map are shown)
    Simple / Loop / Parallel /  switch between the four example graphs
      Loop + parallel
    + loop at v / − loop at v   add or remove a loop at v
    + parallel at v /           add a second (or third) copy of an edge at v, or remove one
      − parallel at v
    Reset                       restore the current example and the starting vertex
    ◀ Previous / Next ▶         move through the walkthrough (also ← / → keys)
"""

from __future__ import annotations

import argparse
import math
import sys
import textwrap
from itertools import combinations, combinations_with_replacement, product
from pathlib import Path

import matplotlib

# Pick a file-only backend before pyplot is imported when no window will be opened.
if "--static" in sys.argv or "--snapshots" in sys.argv:
    matplotlib.use("Agg")

import matplotlib.patheffects as pe
import matplotlib.pyplot as plt
import networkx as nx
from matplotlib.backend_bases import KeyEvent, MouseEvent
from matplotlib.gridspec import GridSpec
from matplotlib.lines import Line2D
from matplotlib.patches import Circle, FancyBboxPatch, Patch, PathPatch
from matplotlib.path import Path as MPath
from matplotlib.widgets import Button

PROJECT_ROOT = Path(__file__).resolve().parent.parent
PROOF_FILE = PROJECT_ROOT / "GraphCh10" / "Exercises" / "Supp10b.lean"
DEFS_FILE = PROJECT_ROOT / "GraphCh10" / "Definitions.lean"

# The theorem statement approved by the project owner (checked against the Lean file).
APPROVED_STATEMENT = [
    "theorem supp10b {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] (G : UGraph V E) :",
    "    (∀ v : V, (G.nbrFinset v).card = G.deg v) ↔ G.IsSimple := by",
]

Ends = dict[str, frozenset]


def _require(path: Path) -> list[str]:
    if not path.exists():
        sys.exit(f"error: cannot find {path}; run this script inside the GraphCh10 project")
    return path.read_text(encoding="utf-8").splitlines()


# ---------------------------------------------------------------------------
# 1. The definitions, mirroring GraphCh10/Definitions.lean and Supp10b.lean
# ---------------------------------------------------------------------------

def names(ends: Ends) -> list[str]:
    """Edge names e0, e1, … in numeric order (edge `i : Fin m` in Lean)."""
    return sorted(ends, key=lambda e: int(e[1:]))


def is_loop(ends: Ends, e: str) -> bool:
    """`IsLoop e := (G.ends e).IsDiag`: the set associated to e has one element."""
    return len(ends[e]) == 1


def adj(ends: Ends, u: int, w: int) -> bool:
    """`Adj u w := ∃ e : E, G.ends e = s(u, w)`."""
    return any(s == frozenset({u, w}) for s in ends.values())


def incident(ends: Ends, e: str, v: int) -> bool:
    """`Incident e v := v ∈ G.ends e`."""
    return v in ends[e]


def incident_edges(ends: Ends, v: int) -> list[str]:
    """`incidentEdges v := Finset.univ.filter (fun e => G.Incident e v)`: I(v)."""
    return [e for e in names(ends) if incident(ends, e, v)]


def loops_at(ends: Ends, v: int) -> list[str]:
    """`loopsAt v := Finset.univ.filter (fun e => G.ends e = s(v, v))`: L(v)."""
    return [e for e in names(ends) if ends[e] == frozenset({v})]


def deg(ends: Ends, v: int) -> int:
    """`deg v := #{e | Incident e v} + #{e | ends e = s(v, v)}` (loops counted twice)."""
    return len(incident_edges(ends, v)) + len(loops_at(ends, v))


def nbr_finset(ends: Ends, v: int, vs: list[int]) -> list[int]:
    """`nbrFinset v := Finset.univ.filter (fun u => G.Adj v u)`: N(v)."""
    return [u for u in vs if adj(ends, v, u)]


def multiple_edge_pairs(ends: Ends) -> list[tuple[str, str]]:
    """Witnesses of `HasMultipleEdges`: distinct edges e₁, e₂ with ends e₁ = ends e₂."""
    return [(a, b) for a, b in combinations(names(ends), 2) if ends[a] == ends[b]]


def is_simple(ends: Ends) -> bool:
    """`IsSimple := ¬ G.HasMultipleEdges ∧ ∀ e : E, ¬ G.IsLoop e`."""
    return not multiple_edge_pairs(ends) and not any(is_loop(ends, e) for e in ends)


def other_end(ends: Ends, v: int, e: str) -> int:
    """`otherEnd v e := if h : v ∈ G.ends e then Sym2.Mem.other h else v`: for e = {v, u}
    the vertex u, for a loop {v} the vertex v itself, and v for edges not at v."""
    if v in ends[e]:
        rest = ends[e] - {v}
        return next(iter(rest)) if rest else v
    return v


def collisions(ends: Ends, v: int) -> dict[int, list[str]]:
    """Where `otherEnd v` is NOT one-to-one on I(v): other endpoint u ↦ the ≥ 2 edges of I(v)
    sent to u. Empty exactly when `Set.InjOn (otherEnd G v) (incidentEdges G v)` holds."""
    groups: dict[int, list[str]] = {}
    for e in incident_edges(ends, v):
        groups.setdefault(other_end(ends, v, e), []).append(e)
    return {u: es for u, es in groups.items() if len(es) > 1}


def vinfo(ends: Ends, v: int, vs: list[int]) -> dict:
    """Everything the pictures show about one vertex v."""
    I, L, N = incident_edges(ends, v), loops_at(ends, v), nbr_finset(ends, v, vs)
    col = collisions(ends, v)
    return dict(v=v, I=I, L=L, N=N, deg=deg(ends, v), col=col, inj=not col,
                gap=deg(ends, v) - len(N), gap_loops=len(L), gap_col=len(I) - len(N),
                eq=len(N) == deg(ends, v))


# ---------------------------------------------------------------------------
# 2. Examples (illustrations only, defined here)
# ---------------------------------------------------------------------------

def as_map(sets: list[set[int]]) -> Ends:
    """Edge i is named e{i}; each value is the set {u, w} (or {v} for a loop)."""
    return {f"e{i}": frozenset(s) for i, s in enumerate(sets)}


N_V = 5
# A 5-cycle 0-1-2-3-4-0 with the chord {1, 3}: a simple graph.
SIMPLE_SETS = [{0, 1}, {1, 2}, {2, 3}, {3, 4}, {4, 0}, {1, 3}]
EXAMPLES: dict[str, tuple[str, Ends]] = {
    "simple": ("Simple graph", as_map(SIMPLE_SETS)),
    "loop": ("Graph with a loop", as_map(SIMPLE_SETS + [{1}])),
    "parallel": ("Graph with parallel edges", as_map(SIMPLE_SETS + [{1, 2}])),
    "both": ("Loops and parallel edges", as_map(SIMPLE_SETS + [{1, 2}, {1}, {3, 4}])),
}
EXAMPLE_ORDER = ["simple", "loop", "parallel", "both"]
START_EXAMPLE = "both"
START_V = 1
MAX_LOOPS_AT_V = 3
MAX_COPIES = 3


def all_graphs(n: int, max_m: int):
    """Every UGraph with vertices 0..n-1 and edges e0..e{m-1}, m ≤ max_m: each edge gets any
    one- or two-element set of vertices."""
    options = [frozenset(p) for p in combinations_with_replacement(range(n), 2)]
    for m in range(max_m + 1):
        for choice in product(options, repeat=m):
            yield {f"e{i}": s for i, s in enumerate(choice)}


# ---------------------------------------------------------------------------
# 3. Programmatic checks
# ---------------------------------------------------------------------------

def check_statement() -> None:
    """The Lean file still contains exactly the approved theorem statement."""
    lines = _require(PROOF_FILE)
    i = next(i for i, ln in enumerate(lines) if ln.startswith("theorem supp10b"))
    assert lines[i:i + 2] == APPROVED_STATEMENT, "the statement of supp10b has changed"


def check_graph(ends: Ends, vs: list[int]) -> bool:
    """Check every lemma of Supp10b.lean on one graph (and cross-check with NetworkX).
    Returns whether |N(v)| = deg v at every vertex."""
    G = nx.MultiGraph()
    G.add_nodes_from(vs)
    G.add_edges_from(tuple(s) * (2 if len(s) == 1 else 1) for s in ends.values())
    all_eq = True
    for v in vs:
        I, L, N = incident_edges(ends, v), loops_at(ends, v), nbr_finset(ends, v, vs)
        assert G.degree(v) == deg(ends, v)                                   # deg = nx degree
        assert set(G.neighbors(v)) == set(N)                                 # N(v) = nx nbrs
        assert deg(ends, v) == len(I) + len(L)                               # deg_eq
        for e in I:                                                          # ends_eq_of_incident
            assert ends[e] == frozenset({v, other_end(ends, v, e)})
        assert {other_end(ends, v, e) for e in I} == set(N)                  # image_otherEnd
        inj = len({other_end(ends, v, e) for e in I}) == len(I)
        assert inj == (not collisions(ends, v))
        eq = len(N) == deg(ends, v)
        assert eq == (len(L) == 0 and inj)                                   # card_nbr_eq_deg_iff
        all_eq &= eq
    assert all_eq == is_simple(ends)                                         # supp10b
    return all_eq


def run_checks() -> dict:
    """Assert every fact the pictures and the walkthrough rely on. Returns summary numbers."""
    check_statement()
    vs = list(range(N_V))
    expected = {"simple": True, "loop": False, "parallel": False, "both": False}
    for key, (_label, ends) in EXAMPLES.items():
        assert check_graph(ends, vs) == expected[key] == is_simple(ends), key
    # The examples show the intended effects at the starting vertex v = 1.
    a = vinfo(EXAMPLES["loop"][1], START_V, vs)
    assert a["gap_loops"] == 1 and a["gap_col"] == 0 and START_V in a["N"]
    b = vinfo(EXAMPLES["parallel"][1], START_V, vs)
    assert b["gap_loops"] == 0 and b["gap_col"] == 1
    c = vinfo(EXAMPLES["both"][1], START_V, vs)
    assert c["gap_loops"] == 1 and c["gap_col"] == 1

    n_graphs = n_simple = 0
    for n in range(1, 5):
        for ends in all_graphs(n, 4):
            n_graphs += 1
            n_simple += check_graph(ends, list(range(n)))
    return dict(n_graphs=n_graphs, n_simple=n_simple)


# ---------------------------------------------------------------------------
# 4. Shared drawing helpers
# ---------------------------------------------------------------------------

COLOR_VERTEX = "#3B6FB6"   # blue vertex fill
COLOR_INC = "#2A9D8F"      # teal: an edge at v whose other endpoint no other edge at v has
COLOR_PAR = "#E08A2C"      # orange: parallel edges (same other endpoint)
COLOR_LOOP = "#C0392B"     # red: a loop
COLOR_NBR = "#1E8C45"      # green: a neighbour of v / a check that holds
COLOR_FOCUS = "#F2B705"    # gold: what the current walkthrough step is about
COLOR_EDGE = "#BDBDBD"     # an edge not at v
COLOR_TEXT = "#222222"
COLOR_WARN = "#B03A2E"
COLOR_CODE_BG = "#FBFBF8"
COLOR_CODE_HL = "#FFF1B8"

NODE_R = 0.27   # node radius in data units
RING = 1.75     # vertices sit on a circle of this radius
LOOP_R = 0.31   # loop circle radius
LOOP_ANGLES = (68, -68, 135, -135)  # loop directions, degrees from "outward"


def positions(n: int) -> dict[int, tuple[float, float]]:
    """Vertices evenly spaced on a circle, vertex 0 at the top, going clockwise."""
    return {i: (RING * math.sin(2 * math.pi * i / n), RING * math.cos(2 * math.pi * i / n))
            for i in range(n)}


def outward(p: tuple[float, float]) -> tuple[float, float]:
    r = math.hypot(*p)
    return (0.0, 1.0) if r < 1e-9 else (p[0] / r, p[1] / r)


def rotate(d: tuple[float, float], deg_: float) -> tuple[float, float]:
    c, s = math.cos(math.radians(deg_)), math.sin(math.radians(deg_))
    return c * d[0] - s * d[1], s * d[0] + c * d[1]


def edge_control(pos, ends: Ends, e: str) -> tuple[tuple, tuple, tuple]:
    """(start, control, end) of the quadratic Bézier drawing a non-loop edge. Parallel edges
    (same set of ends) get different bends so that each one is visible."""
    u, w = sorted(ends[e])
    group = [x for x in names(ends) if ends[x] == ends[e]]
    rad = (group.index(e) - (len(group) - 1) / 2) * 0.42
    (x1, y1), (x2, y2) = pos[u], pos[w]
    c = ((x1 + x2) / 2 + rad * (y2 - y1), (y1 + y2) / 2 - rad * (x2 - x1))
    return (x1, y1), c, (x2, y2)


def bezier(p0, c, p1, t: float) -> tuple[float, float]:
    return ((1 - t) ** 2 * p0[0] + 2 * (1 - t) * t * c[0] + t ** 2 * p1[0],
            (1 - t) ** 2 * p0[1] + 2 * (1 - t) * t * c[1] + t ** 2 * p1[1])


def loop_geometry(pos, ends: Ends, e: str, r: float = NODE_R):
    """Centre of the loop circle and the position of its label."""
    (v,) = tuple(ends[e])
    j = [x for x in names(ends) if ends[x] == ends[e]].index(e) % len(LOOP_ANGLES)
    d = rotate(outward(pos[v]), LOOP_ANGLES[j])
    x, y = pos[v]
    centre = (x + (r + LOOP_R * 0.95) * d[0], y + (r + LOOP_R * 0.95) * d[1])
    label = (x + (r + LOOP_R * 2.45) * d[0], y + (r + LOOP_R * 2.45) * d[1])
    return centre, label


def v_colors(ends: Ends, v: int | None) -> dict[str, str]:
    """Edges at v: teal (other endpoint unique), orange (parallel: shared other endpoint),
    red (loop at v). Other edges are left grey."""
    if v is None:
        return {}
    col = collisions(ends, v)
    out = {}
    for e in incident_edges(ends, v):
        if is_loop(ends, e):
            out[e] = COLOR_LOOP
        elif other_end(ends, v, e) in col:
            out[e] = COLOR_PAR
        else:
            out[e] = COLOR_INC
    return out


def offender_colors(ends: Ends) -> dict[str, str]:
    """All loops red, all (non-loop) multiple edges orange: what stops G being simple."""
    out = {}
    for a, b in multiple_edge_pairs(ends):
        for e in (a, b):
            out[e] = COLOR_LOOP if is_loop(ends, e) else COLOR_PAR
    for e in ends:
        if is_loop(ends, e):
            out[e] = COLOR_LOOP
    return out


def draw_graph(ax, ends: Ends, vs: list[int], edge_colors: dict[str, str] | None = None,
               emphasized: frozenset = frozenset(), tags: dict[int, str] | None = None,
               rings: frozenset = frozenset(), chosen: int | None = None, badges: bool = True,
               labels: bool = True, fontsize: float = 14, width: float = 2.6) -> list:
    """Draw edges and vertices. Coloured edges (others grey) get their name; `emphasized`
    edges are thick with a dark outline; `tags` adds a gold halo and a label; `rings` are
    green outlines (neighbours of v); `badges` shows 'N a · deg b' next to each vertex
    (red when a ≠ b). Returns the label Text objects (for overlap checks)."""
    pos = positions(len(vs))
    edge_colors = edge_colors or {}
    tags = tags or {}
    r = NODE_R
    label_texts = []
    for e in names(ends):
        color = edge_colors.get(e, COLOR_EDGE)
        lw, z = width, 2
        if e in emphasized:
            lw, z = width * 1.5, 2.6
        if is_loop(ends, e):
            centre, (lx, ly) = loop_geometry(pos, ends, e)
            patch = Circle(centre, LOOP_R, fill=False, edgecolor=color, linewidth=lw,
                           zorder=z, linestyle=(0, (4, 2)))
        else:
            p0, c, p1 = edge_control(pos, ends, e)
            patch = PathPatch(MPath([p0, c, p1], [MPath.MOVETO, MPath.CURVE3, MPath.CURVE3]),
                              fill=False, edgecolor=color, linewidth=lw, zorder=z,
                              capstyle="round")
            lx, ly = bezier(p0, c, p1, 0.5)
        if e in emphasized:
            patch.set_path_effects([pe.Stroke(linewidth=lw * 2.0, foreground="#333333"),
                                    pe.Normal()])
        ax.add_patch(patch)
        if labels and (e in edge_colors or e in emphasized):
            label_texts.append(ax.text(
                lx, ly, e, fontsize=fontsize * 0.58, color="#333333", ha="center",
                va="center", zorder=3, bbox=dict(boxstyle="round,pad=0.12", fc="white",
                                                 ec="none", alpha=0.92)))
    for v in vs:
        x, y = pos[v]
        if v in tags:
            ax.add_patch(Circle((x, y), r + 0.16, facecolor=COLOR_FOCUS, alpha=0.6,
                                edgecolor="none", zorder=3.5))
        if v in rings:
            ax.add_patch(Circle((x, y), r + 0.07, fill=False, edgecolor=COLOR_NBR,
                                linewidth=3.2, zorder=4.2))
        ax.add_patch(Circle((x, y), r, facecolor=COLOR_VERTEX, edgecolor="#2A4F85",
                            linewidth=1.5, zorder=4))
        ax.text(x, y, str(v), ha="center", va="center", fontsize=fontsize, fontweight="bold",
                color="white", zorder=5)
        dx, dy = outward(pos[v])
        if badges:
            nv, dv = len(nbr_finset(ends, v, vs)), deg(ends, v)
            bold = v == chosen
            ok = nv == dv
            bx, by = x + dx * (r + 0.78), y + dy * (r + 0.52)
            label_texts.append(ax.text(
                bx, by, f"N {nv} · deg {dv}", ha="center", va="center",
                fontsize=fontsize * (0.64 if bold else 0.58),
                fontweight="bold" if bold else "normal", zorder=6,
                color=COLOR_TEXT if ok else COLOR_WARN,
                bbox=dict(boxstyle="round,pad=0.2", fc="#E8F5EC" if ok else "#FBE3E3",
                          ec=COLOR_FOCUS if bold else ("#9CCBA8" if ok else "#E3A39C"),
                          linewidth=2 if bold else 1)))
        if v in tags:
            tx, ty = x - dx * (r + 0.36), y - dy * (r + 0.36)  # inside the ring
            label_texts.append(ax.text(
                tx, ty, tags[v], ha="center", va="center", fontsize=fontsize * 0.64,
                fontweight="bold", color="#5A4500", zorder=6,
                bbox=dict(boxstyle="round,pad=0.15", fc="#FFF4C2", ec=COLOR_FOCUS)))
    return label_texts


def frame(ax, xlim=(-3.25, 3.25), ylim=(-2.55, 2.75)) -> None:
    ax.set_xlim(*xlim)
    ax.set_ylim(*ylim)
    ax.set_aspect("equal")
    ax.axis("off")


def fmt_edges(es: list[str]) -> str:
    return "{" + ", ".join(es) + "}" if es else "∅"


def fmt_vs(us) -> str:
    return "{" + ", ".join(map(str, us)) + "}" if us else "∅"


def fmt_set(s: frozenset) -> str:
    return "{" + ", ".join(map(str, sorted(s))) + "}"


def _yn(b: bool) -> str:
    return "yes" if b else "no"


def _rel(a: int, b: int) -> str:
    return "=" if a == b else "<"


def map_rows(ends: Ends, v: int) -> list[tuple[str, str, int]]:
    """The rows of the other-endpoint panel: one per unit of deg v. (edge, kind, target):
    kind 'edge' / 'loop' for each e ∈ I(v) (target = otherEnd v e), and 'again' for the
    second count of each loop (no target)."""
    rows = []
    I = incident_edges(ends, v)
    for e in sorted(I, key=lambda x: (other_end(ends, v, x), int(x[1:]))):
        if is_loop(ends, e):
            rows.append((e, "loop", v))
            rows.append((e, "again", v))
        else:
            rows.append((e, "edge", other_end(ends, v, e)))
    return rows


def draw_map(ax, ends: Ends, v: int, vs: list[int], fs: float = 9.5,
             title: str | None = None) -> None:
    """The other-endpoint map at v: each unit of deg v on the left (solid = an edge of I(v),
    dashed = a loop counted again), arrows e ↦ otherEnd v e to N(v) on the right, then the
    chain |N(v)| ≤ |I(v)| ≤ deg v."""
    ax.clear()
    ax.set_xlim(0, 1)
    ax.set_ylim(0, 1)
    ax.axis("off")
    ax.add_patch(plt.Rectangle((0, 0), 1, 1, transform=ax.transAxes, facecolor="#F7F7F7",
                               edgecolor="#D0D0D0"))
    info = vinfo(ends, v, vs)
    ax.text(0.5, 0.975, title or f"Other-endpoint map at v = {v}", ha="center", va="top",
            fontsize=fs + 1, fontweight="bold", color=COLOR_TEXT)
    ax.text(0.26, 0.905, "deg v: edges at v", ha="center", va="center", fontsize=fs - 0.8,
            color="#555555", fontweight="bold")
    ax.text(0.86, 0.905, "N(v)", ha="center", va="center", fontsize=fs - 0.8,
            color=COLOR_NBR, fontweight="bold")
    rows = map_rows(ends, v)
    top, bottom = 0.84, 0.36
    if not rows:
        ax.text(0.5, 0.6, "no edges at v:\nI(v) = ∅, N(v) = ∅", ha="center", va="center",
                fontsize=fs)
    step = min(0.085, (top - bottom) / max(len(rows) - 1, 1))
    span = step * (len(rows) - 1)
    y0 = (top + bottom) / 2 + span / 2
    row_fs = fs - 0.6 if step >= 0.06 else fs - 1.8
    ys = [y0 - i * step for i in range(len(rows))]
    targets: dict[int, list[float]] = {}
    for (e, kind, t), y in zip(rows, ys):
        if kind != "again":
            targets.setdefault(t, []).append(y)
    t_y = {t: sum(yy) / len(yy) for t, yy in targets.items()}
    for (e, kind, t), y in zip(rows, ys):
        if kind == "again":
            txt, col, fc, ls = f"{e} again: no arrow", COLOR_LOOP, "#FBE9E7", "--"
        elif kind == "loop":
            txt, col, fc, ls = f"{e} = {{{v}}} loop", COLOR_LOOP, "#FBE9E7", "-"
        else:
            par = t in info["col"]
            txt = f"{e} = {fmt_set(ends[e])}"
            col, fc, ls = (COLOR_PAR, "#FDF0E1", "-") if par else (COLOR_INC, "#E3F4F1", "-")
        ax.text(0.26, y, txt, ha="center", va="center", fontsize=row_fs, color=COLOR_TEXT,
                bbox=dict(boxstyle="round,pad=0.25", fc=fc, ec=col, linestyle=ls,
                          linewidth=1.4))
        if kind != "again":  # a loop's second count gets no arrow: no new neighbour
            col = COLOR_LOOP if kind == "loop" else (COLOR_PAR if t in info["col"] else COLOR_INC)
            ax.annotate("", xy=(0.81, t_y[t]), xytext=(0.5, y),
                        arrowprops=dict(arrowstyle="-|>", color=col, lw=1.6,
                                        shrinkA=2, shrinkB=9, mutation_scale=11))
    for t, y in t_y.items():
        ax.text(0.86, y, str(t), ha="center", va="center", fontsize=fs + 0.5,
                fontweight="bold", color="white",
                bbox=dict(boxstyle="circle,pad=0.3", fc=COLOR_VERTEX, ec=COLOR_NBR, lw=2.2))
        if t in info["col"]:  # several edges land here: the map is not one-to-one
            ax.text(0.945, y, f"×{len(info['col'][t])}", ha="center", va="center",
                    fontsize=row_fs, color=COLOR_PAR, fontweight="bold")
        if t == v:  # a loop's other endpoint is v itself
            ax.text(0.86, y - 0.05, "v itself", ha="center", va="top",
                    fontsize=row_fs - 1.5, color="#555555", fontweight="bold")
    nI, nL, nN, d = len(info["I"]), len(info["L"]), len(info["N"]), info["deg"]
    ax.plot([0.03, 0.97], [0.29, 0.29], color="#D0D0D0", lw=1)
    ax.text(0.5, 0.235, f"|N(v)| = {nN}  {_rel(nN, nI)}  |I(v)| = {nI}  {_rel(nI, d)}  "
            f"deg v = {d}", ha="center", va="center", fontsize=fs, fontweight="bold",
            color=COLOR_TEXT, family="DejaVu Sans Mono")
    ax.text(0.5, 0.15, f"gap deg v − |N(v)| = {info['gap']}:  {info['gap_loops']} from loops,"
            f"\n{info['gap_col']} from repeated other endpoints", ha="center", va="center",
            fontsize=fs - 1, color="#444444", linespacing=1.25)
    ok = info["eq"]
    ax.text(0.5, 0.05, "|N(v)| = deg v  ✓" if ok else "|N(v)| ≠ deg v  ✗", ha="center",
            va="center", fontsize=fs + 0.5, fontweight="bold",
            color=COLOR_NBR if ok else COLOR_WARN)


def legend_handles() -> list:
    return [
        Patch(facecolor=COLOR_VERTEX, edgecolor="#2A4F85", label="vertex"),
        Line2D([], [], color=COLOR_INC, linewidth=3, label="edge at v"),
        Line2D([], [], color=COLOR_PAR, linewidth=3, label="parallel edges at v"),
        Line2D([], [], color=COLOR_LOOP, linewidth=3, linestyle="--", label="loop"),
        Line2D([], [], color=COLOR_EDGE, linewidth=3, label="other edge"),
        Line2D([], [], marker="o", linestyle="none", markersize=13, markerfacecolor="white",
               markeredgecolor=COLOR_NBR, markeredgewidth=2.5, label="neighbour of v"),
        Patch(facecolor=COLOR_FOCUS, alpha=0.6, label="gold: this step"),
    ]


# ---------------------------------------------------------------------------
# 5. Static summary figure (visualizations/supp10b.png)
# ---------------------------------------------------------------------------

def build_figure(stats: dict) -> plt.Figure:
    fig = plt.figure(figsize=(19, 14.5), facecolor="white")
    gs = GridSpec(3, 4, figure=fig, height_ratios=[0.8, 1.05, 0.5], hspace=0.16, wspace=0.08,
                  left=0.03, right=0.97, top=0.875, bottom=0.03)
    vs = list(range(N_V))
    fig.suptitle("Supplementary Exercise 10(b):   |N(v)| = deg v for every v   ⇔   G is simple",
                 fontsize=19, fontweight="bold", color=COLOR_TEXT, y=0.985)
    fig.text(0.5, 0.957,
             "\"Let G = (V, E) be an undirected graph. Show that |N(v)| = deg v for all v ∈ V "
             "if and only if G is a simple graph.\"   Proved in Lean as GraphCh10.supp10b.",
             ha="center", fontsize=10.5, color="#444444")
    fig.text(0.5, 0.94,
             "Each picture is one graph: it illustrates the theorem, it does not prove it. "
             "The Lean proof covers every finite graph.   Run  python visualizations/supp10b.py"
             "  for the interactive walkthrough.", ha="center", fontsize=10.5, color=COLOR_WARN,
             style="italic")

    for col, key in enumerate(EXAMPLE_ORDER):
        label, ends = EXAMPLES[key]
        ax = fig.add_subplot(gs[0, col])
        info = vinfo(ends, START_V, vs)
        draw_graph(ax, ends, vs, v_colors(ends, START_V), tags={START_V: "v"},
                   rings=frozenset(info["N"]), chosen=START_V)
        frame(ax)
        simple = is_simple(ends)
        all_eq = all(vinfo(ends, w, vs)["eq"] for w in vs)
        ax.set_title(label, fontsize=13.5, fontweight="bold", pad=26)
        ax.text(0.5, 1.02, f"simple? {_yn(simple)}    |N(v)| = deg v for all v? {_yn(all_eq)}",
                transform=ax.transAxes, ha="center", va="bottom", fontsize=10.5,
                fontweight="bold", color=COLOR_NBR if simple else COLOR_WARN)

    captions = {
        "simple": "every edge at 1 reaches a different neighbour",
        "loop": "the loop e6 is counted twice in deg 1,\nbut adds only one neighbour: 1 itself",
        "parallel": "e1 and e6 both go to 2:\none extra unit of degree, no new neighbour",
        "both": "both effects at once: gap 2",
    }
    for col, key in enumerate(EXAMPLE_ORDER):
        label, ends = EXAMPLES[key]
        ax = fig.add_subplot(gs[1, col])
        draw_map(ax, ends, START_V, vs, fs=10.5, title=f"{label}: map at v = {START_V}")
        ax.text(0.5, -0.03, captions[key], transform=ax.transAxes, ha="center", va="top",
                fontsize=10, color="#444444", style="italic")

    ax = fig.add_subplot(gs[2, :])
    ax.axis("off")
    ax.add_patch(plt.Rectangle((0, 0), 1, 1, transform=ax.transAxes, facecolor="#F7F7F7",
                               edgecolor="#D0D0D0", linewidth=1))
    left = ["The Lean proof  (GraphCh10/Exercises/Supp10b.lean)",
            "deg_eq               deg v = |I(v)| + |L(v)|       (loops counted a second time)",
            "image_otherEnd       otherEnd v maps I(v) ONTO N(v), so |N(v)| ≤ |I(v)| ≤ deg v",
            "card_nbr_eq_deg_iff  |N(v)| = deg v  ⇔  L(v) = ∅  and  otherEnd v one-to-one on I(v)",
            "supp10b (⇒)          a loop at a: L(a) ≠ ∅ ✗;  parallel e₁, e₂ on {a, b}: both ↦ b ✗",
            "supp10b (⇐)          simple: no loops at v, and same other endpoint ⇒ same edge"]
    right = ["Checked by assertions in this script",
             "• the theorem statement in Supp10b.lean is the approved one",
             f"• all {stats['n_graphs']:,} graphs with ≤ 4 vertices and ≤ 4 edges (loops and",
             f"  multiple edges allowed; {stats['n_simple']:,} simple): every lemma above holds",
             "  at every vertex, and NetworkX agrees on deg and N(v)",
             "• this is evidence only; the Lean proof is the proof"]
    for x, lines in ((0.012, left), (0.6, right)):
        ax.text(x, 0.9, lines[0], transform=ax.transAxes, fontsize=11.5, fontweight="bold",
                va="top", color=COLOR_TEXT)
        ax.text(x, 0.7, "\n".join(lines[1:]), transform=ax.transAxes, fontsize=9.8,
                va="top", color=COLOR_TEXT, family="DejaVu Sans Mono" if x < 0.5 else None,
                linespacing=1.6)
    fig.legend(handles=legend_handles(), loc="upper center", ncol=7, frameon=False,
               fontsize=10.5, bbox_to_anchor=(0.5, 0.932))
    return fig


# ---------------------------------------------------------------------------
# 6. Lean source, read from the project (the source of truth)
# ---------------------------------------------------------------------------

def _start(lines: list[str], start: str) -> int:
    hits = [i for i, ln in enumerate(lines) if ln.strip().startswith(start)]
    assert len(hits) == 1, f"expected exactly one line starting with {start!r}"
    return hits[0]


def _block(lines: list[str], start: str, end: str, doc: bool = False) -> list[str]:
    """The lines from the unique line starting with `start` (and, with `doc`, its docstring
    just above) to the first later line containing `end` (inclusive)."""
    i = _start(lines, start)
    j = next(j for j in range(i, len(lines)) if end in lines[j])
    if doc and i > 0 and lines[i - 1].rstrip().endswith("-/"):
        i -= 1
        while not lines[i].lstrip().startswith("/--"):
            i -= 1
    return [ln.rstrip() for ln in lines[i:j + 1]]


def read_lean_sources() -> dict[str, list[str]]:
    """The proof of `supp10b`, its helpers and the definitions, read verbatim."""
    proof = _require(PROOF_FILE)
    def_lines = _require(DEFS_FILE)
    phase2 = _start(def_lines, "/-! ## Phase 2: simple undirected graphs")

    def find(prefix: str, extra: int = 0, after: int = 0) -> list[str]:
        hits = [i for i, ln in enumerate(def_lines) if i >= after and
                ln.strip().startswith(prefix)]
        assert len(hits) == 1, f"expected exactly one line starting with {prefix!r}"
        return [ln.rstrip() for ln in def_lines[hits[0]:hits[0] + extra + 1]]

    defs = [
        "-- GraphCh10/Definitions.lean (excerpt; docstrings omitted)",
        *find("structure UGraph"),
        *find("ends : E → Sym2 V"),
        "",
        "namespace UGraph   -- inside: variable (G : UGraph V E)",
        *find("def IsLoop (e : E) : Prop := (G.ends e).IsDiag"),
        *find("def HasMultipleEdges", after=phase2),
        *find("def IsSimple", after=phase2),
        "",
        *find("def Adj"),
        *find("def nbhd (v : V)"),
        *find("def nbrFinset", extra=1),
        "",
        *find("def Incident"),
        *find("def deg", extra=2),
    ]
    return {
        "defs": defs,
        "header": _block(proof, "Paper proof. Fix a vertex v.",
                         "Both contradict |N(a)| = deg a, so G is simple."),
        "aux": _block(proof, "def incidentEdges", "exact Sym2.congr_right.mp hboth", doc=True),
        "deg": _block(proof, "theorem deg_eq", "rfl", doc=True),
        "image": _block(proof, "theorem image_otherEnd",
                        "exact ⟨e, hinc, otherEnd_eq_of_ends G he⟩", doc=True),
        "iff": _block(proof, "theorem card_nbr_eq_deg_iff", "omega", doc=True),
        "main": _block(proof, "theorem supp10b", "exact hNoMultiple ⟨e₁, e₂, hne, hsameEnds⟩",
                       doc=True),
    }


SOURCE_NAMES = {
    "defs": "GraphCh10/Definitions.lean",
    "header": "Supp10b.lean  ·  file comment (paper proof)",
    "aux": "Supp10b.lean  ·  I(v), L(v), otherEnd and two facts",
    "deg": "Supp10b.lean  ·  lemma deg_eq",
    "image": "Supp10b.lean  ·  lemma image_otherEnd",
    "iff": "Supp10b.lean  ·  key lemma card_nbr_eq_deg_iff",
    "main": "Supp10b.lean  ·  the main theorem supp10b",
}


# ---------------------------------------------------------------------------
# 7. The walkthrough
# ---------------------------------------------------------------------------
# Each step: part, title, code source, `anchors` (substrings that must each match exactly one
# line) and `ranges` ((first, last): the unique line containing `first` through the next line
# containing `last`), a graph focus, and two explanations: `math` (graph-theory idea) and
# `lean` (Lean syntax). Both may be functions of the explorer.

P1, P2, P3, P4, P5 = ("Part 1 · Graph basics", "Part 2 · Why it is true",
                      "Part 3 · Lean: helper definitions and lemmas",
                      "Part 4 · Lean: the main theorem", "Part 5 · Example vs. proof")


def _vi(ex) -> dict:
    return vinfo(ex.ends, ex.selected, ex.vs)


def _offenders(ex) -> str:
    loops = [e for e in names(ex.ends) if is_loop(ex.ends, e)]
    groups: dict[frozenset, list[str]] = {}
    for e in names(ex.ends):
        groups.setdefault(ex.ends[e], []).append(e)
    mult = [es for s, es in groups.items() if len(es) > 1]
    a = ("loops: " + ", ".join(f"{e} = {fmt_set(ex.ends[e])}" for e in loops)) if loops \
        else "no loops"
    b = ("multiple edges: " + "; ".join(" and ".join(es) + f" (both {fmt_set(ex.ends[es[0]])})"
                                         for es in mult)) if mult else "no multiple edges"
    return f"{a}; {b}"


def _counts(ex) -> str:
    i = _vi(ex)
    return (f"For v = {i['v']}: I(v) = {fmt_edges(i['I'])}, L(v) = {fmt_edges(i['L'])}, "
            f"N(v) = {fmt_vs(i['N'])}; |N(v)| = {len(i['N'])}, |I(v)| = {len(i['I'])}, "
            f"deg v = {i['deg']}.")


def _gap(ex) -> str:
    i = _vi(ex)
    if i["eq"]:
        return (f"For v = {i['v']}: no loops and no repeated other endpoints, so |N(v)| = "
                f"deg v = {i['deg']}.")
    return (f"For v = {i['v']}: gap deg v − |N(v)| = {i['gap']} = {i['gap_loops']} (loops) + "
            f"{i['gap_col']} (repeated other endpoints).")


def _all_line(ex) -> str:
    bad = [w for w in ex.vs if not vinfo(ex.ends, w, ex.vs)["eq"]]
    s = is_simple(ex.ends)
    return (f"Right now: |N(v)| = deg v at every vertex? {_yn(not bad)}"
            + (f" (fails at {fmt_vs(bad)})" if bad else "") + f"; simple? {_yn(s)}. "
            "The two answers always agree: that is the theorem.")


def _map_example(ex) -> str:
    i = _vi(ex)
    parts = [f"{e} ↦ {other_end(ex.ends, i['v'], e)}" for e in i["I"]]
    return f"At v = {i['v']}: " + (", ".join(parts) if parts else "no edges") + "."


def _fact_example(ex) -> str:
    i = _vi(ex)
    es = [e for e in i["I"] if not is_loop(ex.ends, e)]
    if not es:
        return ""
    e = es[0]
    u = other_end(ex.ends, i["v"], e)
    return (f" Example at v = {i['v']}: {e} = {fmt_set(ex.ends[e])}, so otherEnd {i['v']} {e} "
            f"= {u} (Fact 2) and {e} = {{{i['v']}, {u}}} (Fact 1).")


def _loop_witness_text(ex, f) -> str:
    if f.get("e") is None:
        return ("This graph has no loop, so there is nothing to rule out here. Press 'Loop' or "
                "'+ loop at v' to see the argument on a real loop.")
    a, e = f["a"], f["e"]
    ia = vinfo(ex.ends, a, ex.vs)
    return (f"Here: {e} is a loop at a = {a}, so {e} ∈ L({a}) and |N({a})| = {len(ia['N'])} ≠ "
            f"deg {a} = {ia['deg']}. So this graph does not satisfy the assumption, exactly as "
            "the argument predicts (dashed row in the map).")


def _multi_witness_text(ex, f) -> str:
    if f.get("pair") is None:
        return ("This graph has no multiple edges, so there is nothing to rule out here. Press "
                "'Parallel' or '+ parallel at v' to see the argument on real parallel edges.")
    (e1, e2), a, b = f["pair"], f["a"], f["b"]
    ia = vinfo(ex.ends, a, ex.vs)
    return (f"Here: {e1} and {e2} both have ends {fmt_set(ex.ends[e1])}; with a = {a}, b = {b} "
            f"both map to {b} (orange arrows in the map), and |N({a})| = {len(ia['N'])} ≠ "
            f"deg {a} = {ia['deg']}.")


STEPS: list[dict] = [
    dict(
        part=P1, title="Undirected graphs: each edge joins a set {u, w}", code="defs",
        anchors=["structure UGraph", "ends : E → Sym2 V"], focus="offenders",
        math=lambda ex, f: (
            "An undirected graph has vertices (blue circles) and edges (lines). Each edge "
            "joins a set of one or two vertices, {u, w}. Two DIFFERENT edges may join the same "
            "two vertices: these are multiple (parallel) edges, drawn as curves side by side. "
            "An edge whose set has just one vertex, {v}, is a loop: a dashed circle at v. "
            f"In this graph: {_offenders(ex)} (highlighted)."),
        lean=("`structure UGraph V E` packages a graph: `V` is the type of vertices, `E` the type "
              "of edges, and the field `ends : E → Sym2 V` gives every edge e its set of "
              "endpoints `G.ends e`. `Sym2 V` is the type of unordered pairs: `s(u, w)` is the "
              "set {u, w}, so `s(u, w) = s(w, u)`, and `s(v, v)` is the one-element set {v} "
              "(a loop). Edges have their own names (e0, e1, …), so two different edges can "
              "have equal `ends`: that is how multiple edges are represented."),
    ),
    dict(
        part=P1, title="Loops, multiple edges, and simple graphs", code="defs",
        anchors=["def IsLoop", "def HasMultipleEdges", "def IsSimple"], focus="offenders",
        math=lambda ex, f: (
            "A graph is SIMPLE when it has no loops and no multiple edges. "
            f"Right now: {_offenders(ex)}; simple? {_yn(is_simple(ex.ends))}. "
            "Use the example buttons, or '+ loop at v' / '+ parallel at v', to change this; "
            "'Reset' restores the example."),
        lean=("`IsLoop e := (G.ends e).IsDiag`: `IsDiag` says the pair has the form s(a, a), a "
              "one-element set. `HasMultipleEdges := ∃ e₁ e₂, e₁ ≠ e₂ ∧ G.ends e₁ = G.ends e₂`: "
              "two DIFFERENT edges with the SAME endpoints. `IsSimple := ¬ G.HasMultipleEdges ∧ "
              "∀ e, ¬ G.IsLoop e`. Symbols: `∃` there exists, `∀` for every, `∧` and, `¬` not, "
              "`≠` not equal, `:=` 'is defined as'. `Prop` is the type of statements (true or "
              "false)."),
    ),
    dict(
        part=P1, title="Neighbours: the set N(v) and its size |N(v)|", code="defs",
        anchors=["def Adj", "def nbhd (v : V)", "def nbrFinset",
                 "Finset.univ.filter (fun u : V => G.Adj v u)"], focus="nbrs",
        math=lambda ex, f: (
            "Two vertices are adjacent (neighbours) when some edge joins them. N(v) is the set "
            "of all neighbours of v (green rings), and |N(v)| is how many there are. A "
            "neighbour counts ONCE, however many edges join it to v. A loop at v makes v its "
            f"own neighbour. For v = {ex.selected}: N(v) = {fmt_vs(_vi(ex)['N'])}, so |N(v)| = "
            f"{len(_vi(ex)['N'])}. Click a vertex to choose another v."),
        lean=("`Adj u w := ∃ e, G.ends e = s(u, w)`: some edge has endpoints {u, w}. `nbhd v` is "
              "the set {u | G.Adj v u}. To COUNT it, Lean needs a finite set (`Finset`): "
              "`nbrFinset v := Finset.univ.filter (fun u => G.Adj v u)`. Read it inside out: "
              "`Finset.univ` is the finite set of all vertices, `.filter p` keeps those "
              "satisfying p, and `fun u => …` is the function sending u to …. Then "
              "`(G.nbrFinset v).card` is |N(v)|: `.card` is the number of elements."),
    ),
    dict(
        part=P1, title="Degree: deg v, with loops counted twice", code="defs",
        anchors=["def Incident"],
        ranges=[("def deg", "(Finset.univ.filter (fun e : E => G.ends e = s(v, v))).card")],
        focus="incident",
        math=lambda ex, f: (
            "An edge is incident with v when v is one of its endpoints. The degree deg v is "
            "the number of edges incident with v, where a loop counts TWICE (both of its ends "
            f"are at v). {_counts(ex)} So deg v = |I(v)| + |L(v)| = {len(_vi(ex)['I'])} + "
            f"{len(_vi(ex)['L'])} = {_vi(ex)['deg']}, where I(v) are the edges at v and L(v) "
            "the loops at v. The left column of the map panel lists one row per unit of deg v."),
        lean=("`Incident e v := v ∈ G.ends e` (`∈` means 'is a member of'). `deg v` adds two "
              "counts: `(Finset.univ.filter (fun e => G.Incident e v)).card`, the number of "
              "edges incident with v, plus `(Finset.univ.filter (fun e => G.ends e = s(v, v))).card`"
              ", the number of loops at v. Adding the loops a second time is exactly 'loops "
              "counted twice'. `[Fintype E]` says there are finitely many edges; `[DecidableEq V]`"
              " lets Lean test vertices for equality while filtering."),
    ),
    dict(
        part=P1, title="Reading the theorem", code="main",
        ranges=[("/-- **Supplementary Exercise 10(b).**", "↔ G.IsSimple := by")],
        focus="vertex",
        math=lambda ex, f: (
            "'If and only if' (⇔) means two claims. (⇒) If every vertex has |N(v)| = deg v, "
            "then G is simple. (⇐) If G is simple, then every vertex has |N(v)| = deg v. The "
            "labels 'N · deg' next to the vertices show both numbers; red means they differ. "
            + _all_line(ex)),
        lean=("`theorem supp10b … : A ↔ B := by …` states 'A if and only if B' (`↔`) and starts "
              "the proof. Before the last colon are the inputs: types `V`, `E` (`Type*` is a "
              "technical size label), the graph `G : UGraph V E`, and assumptions in square "
              "brackets: finitely many vertices and edges, and equality of vertices can be "
              "tested. `∀ v : V, (G.nbrFinset v).card = G.deg v` is '|N(v)| = deg v for every "
              "vertex v'. After `by` come tactics: commands that transform the GOAL (what is "
              "still to be proved) until nothing is left."),
    ),
    dict(
        part=P2, title="The idea: the other-endpoint map", code="header",
        ranges=[("Paper proof. Fix a vertex v.", "Hence |N(v)| = |image|")], focus="vertex",
        math=lambda ex, f: (
            "Fix v. Send each edge e at v to its OTHER ENDPOINT: for e = {v, u} that is u; for "
            "a loop {v} it is v itself. The map panel draws these arrows. Every arrow lands on "
            "a neighbour (e joins v to it), and every neighbour is hit (by an edge joining it "
            "to v). So |N(v)| = number of landing points ≤ |I(v)| ≤ |I(v)| + |L(v)| = deg v. "
            f"{_map_example(ex)}"),
        lean=("Nothing new in Lean yet: this is the comment ('paper proof') at the top of "
              "Supp10b.lean, which the Lean proof follows step by step. 'Onto' means every "
              "neighbour is hit by some arrow. 'One-to-one' means no two arrows land on the "
              "same vertex. |image| is the number of landing points."),
    ),
    dict(
        part=P2, title="Where degree is wasted: loops and parallel edges", code="header",
        anchors=["**|N(v)| = deg v exactly when", "Intuitively, a loop adds 2",
                 "Intuitively, the second parallel edge"], focus="vertex",
        math=lambda ex, f: (
            "|N(v)| = deg v needs BOTH '≤' to be '='. A loop at v adds 2 to deg v but at most "
            "one neighbour (v itself): a dashed row with no arrow. Two parallel edges at v "
            "have the same other endpoint: two arrows land on one neighbour (orange). "
            f"{_gap(ex)} Try '+ loop at v' and '+ parallel at v' and watch the gap grow; the "
            "'−' buttons shrink it again."),
        lean=("Still the file comment. `L(v) = ∅` means 'L(v) is empty' (`∅` is the empty "
              "set). The rest of the proof turns these sentences into Lean: Part 3 proves the "
              "chain and the exact condition for equality, Part 4 uses it for both directions."),
    ),
    dict(
        part=P3, title="Tactic cheat sheet (come back to it)", code="iff",
        anchors=["theorem card_nbr_eq_deg_iff"], focus="vertex",
        math=lambda ex, f: (
            "You do not need to memorise tactics: each step explains its tactics again, and "
            "you can press ◀ Previous to come back here. A CONTRADICTION is having both P and "
            "'not P'. From a contradiction Lean accepts the impossible statement `False`, and "
            "from False anything follows. A proof 'by contradiction' assumes something and "
            "reaches False."),
        lean=("• `intro h` / `rintro ⟨a, b⟩`: assume the 'if' part, name it (rintro also unpacks)\n"
              "• `have h : P := …`: prove a fact P now and name it h   • `exact t`: t proves the goal\n"
              "• `obtain ⟨a, ha⟩ : ∃ a, P a := …`: get a witness a and the fact ha about it\n"
              "• `rw [h]`: rewrite using the equation h (left → right; `← h` for right → left)\n"
              "• `simp only [rules]`: simplify with exactly these rules   • `rfl`: both sides "
              "are the same\n"
              "• `change P`: restate the goal in a form that is equal by definition\n"
              "• `constructor`: split `A ↔ B` (or `A ∧ B`) into two goals   • `ext x`: equal "
              "sets ⇔ same elements\n"
              "• `omega`: solves arithmetic with +, ≤, = on whole numbers\n"
              "• `by_contra h`: assume the opposite (h), prove False   • `absurd h hn`: h and "
              "¬h contradict\n"
              "• `apply f`: f proves the goal once f's own assumptions are proved\n"
              "• `induction x using Sym2.ind`: prove a claim for every pair x by proving it "
              "for each s(a, b)"),
    ),
    dict(
        part=P3, title="Notation cheat sheet (come back to it)", code="iff",
        anchors=["(loopsAt G v).card = 0 ∧ Set.InjOn"], focus="vertex",
        math=lambda ex, f: (
            "Besides tactics, the proof uses some notation. Like the tactic cheat sheet, this "
            "page is for reference."),
        lean=("• `⟨a, b⟩`: bundle parts (a proof of A ∧ B, or of ∃ x, …); `rintro`/`obtain` "
              "unpack it\n"
              "• `h.1`, `h.2`: the two parts of A ∧ B   • `h.mp` / `h.mpr`: use A ↔ B left→right "
              "/ right→left\n"
              "• `h.symm`: from a = b get b = a   • `h₁.trans h₂`: from a = b and b = c get a = c\n"
              "• `Finset`: a finite set; `s.card` its size; `∅` the empty set; `e ∉ s`: not in s\n"
              "• `s.image f`: the set {f x | x ∈ s}   • `fun e => …`: the function e ↦ …\n"
              "• `Set.InjOn f s`: f is one-to-one on s (f x = f y with x, y ∈ s forces x = y)\n"
              "• `·` starts the proof of one goal   • `-- …` is a comment for humans\n"
              "• `namespace Supp10b`: these helper names belong to this exercise only"),
    ),
    dict(
        part=P3, title="I(v) and L(v) as finite sets", code="aux",
        anchors=["def incidentEdges", "Finset.univ.filter (fun e : E => G.Incident e v)",
                 "def loopsAt", "Finset.univ.filter (fun e : E => G.ends e = s(v, v))"],
        focus="incident",
        math=lambda ex, f: (
            f"{_counts(ex)} In the graph, the edges of I(v) are coloured (teal, orange or red), "
            "and the loops of L(v) are the red dashed circles. These are exactly the two sets "
            "whose sizes add up to deg v."),
        lean=("`def incidentEdges v : Finset E := Finset.univ.filter (fun e => G.Incident e v)`: "
              "all edges, filtered to those incident with v. `loopsAt v` keeps the edges with "
              "`G.ends e = s(v, v)`. A `def` gives a name to a construction; `/-- … -/` above it "
              "is its documentation. These two sets are literally the ones inside the "
              "definition of `deg`."),
    ),
    dict(
        part=P3, title="The other-endpoint map otherEnd v e", code="aux",
        anchors=["noncomputable def otherEnd", "if h : v ∈ G.ends e then Sym2.Mem.other h else v"],
        focus="vertex",
        math=lambda ex, f: (
            "otherEnd v e is the vertex at the other end of e, seen from v: u for e = {v, u}, "
            "and v itself for a loop. Only edges at v matter. "
            f"{_map_example(ex)} These are the arrows of the map panel."),
        lean=("`if h : v ∈ G.ends e then … else v` is an if-then-else that also NAMES its "
              "condition h, so the 'then' branch can use it. `Sym2.Mem.other h` is Mathlib's "
              "'the other element of the pair, given that v is in it'. For edges without v the "
              "value is irrelevant, but a Lean function must return something, so it returns "
              "v. `noncomputable`: Lean will not run this as a program (Mathlib defines `other` "
              "by choice); proofs can still use it. This script computes the same value "
              "directly."),
    ),
    dict(
        part=P3, title="Two facts about the other endpoint", code="aux",
        ranges=[("theorem ends_eq_of_incident", "exact Sym2.congr_right.mp hboth")],
        focus="vertex",
        math=lambda ex, f: (
            "Fact 1: if e is incident with v, then e has endpoints {v, otherEnd v e}. Fact 2: "
            "if e has endpoints {v, w}, then otherEnd v e = w." + _fact_example(ex)),
        lean=("Fact 1: `have hmem : v ∈ G.ends e := h` restates h (Incident is defined as ∈). "
              "`simp only [otherEnd, hmem, ↓reduceDIte]` unfolds otherEnd and, since hmem makes "
              "the condition true, picks the 'then' branch. `exact (Sym2.other_spec hmem).symm` "
              "finishes (other_spec: s(v, other) = ends e). Fact 2: `change v ∈ G.ends e` "
              "unfolds the goal; `rw [h]` replaces ends e by s(v, w); `Sym2.mem_mk_left v w` : "
              "v ∈ s(v, w). Then s(v, otherEnd) = s(v, w) via `.symm.trans`, and "
              "`Sym2.congr_right` (s(v, x) = s(v, y) ↔ x = y) cancels v; `.mp` uses it left→right."),
    ),
    dict(
        part=P3, title="deg v = |I(v)| + |L(v)|", code="deg",
        anchors=["theorem deg_eq", "rfl"], focus="incident",
        math=lambda ex, f: (
            "deg v counts every edge at v once and every loop once more. "
            f"For v = {ex.selected}: |I(v)| = {len(_vi(ex)['I'])}, |L(v)| = "
            f"{len(_vi(ex)['L'])}, deg v = {_vi(ex)['deg']}. In the map panel the solid rows are "
            "I(v) and the dashed red rows are the second count of each loop."),
        lean=("`rfl` (reflexivity) proves an equation whose two sides are equal BY DEFINITION. "
              "`deg v` was defined as exactly these two counts added, so nothing needs to be "
              "computed. `G.deg v` is deg v; `(incidentEdges G v).card` is |I(v)|; "
              "`(loopsAt G v).card` is |L(v)|."),
    ),
    dict(
        part=P3, title="The map hits exactly N(v)", code="image",
        ranges=[("theorem image_otherEnd", "exact ⟨e, hinc, otherEnd_eq_of_ends G he⟩")],
        focus="vertex",
        math=lambda ex, f: (
            "Two halves. (1) Every arrow lands in N(v): by Fact 1, e joins v to otherEnd v e, "
            "so they are adjacent. (2) Every neighbour w is hit: an edge e joining v and w is "
            "incident with v and has other endpoint w (Fact 2). So the image of I(v) is "
            f"exactly N(v). For v = {ex.selected}: landing points {fmt_vs(_vi(ex)['N'])} = N(v)."),
        lean=("`(incidentEdges G v).image (otherEnd G v)` is {otherEnd v e | e ∈ I(v)}. `ext w` "
              "reduces equality of finite sets to 'w in one ⇔ w in the other'. `simp only [...]` "
              "unfolds both memberships. `constructor` splits ⇔. `rintro ⟨e, hinc, rfl⟩` unpacks "
              "'there is an e …' and, with `rfl`, replaces w by otherEnd v e everywhere. "
              "`exact ⟨e, …⟩` gives the witness edge e with the proof that it works."),
    ),
    dict(
        part=P3, title="Key lemma: equality ⇔ no loops and one-to-one", code="iff",
        ranges=[("theorem card_nbr_eq_deg_iff", "omega")], focus="vertex",
        math=lambda ex, f: (
            "|N(v)| ≤ |I(v)| ≤ |I(v)| + |L(v)| = deg v. The two ends are equal exactly when "
            "both '≤' are '=': |L(v)| = 0 (no loop at v) and |N(v)| = |I(v)| (the map is "
            "one-to-one: no two edges at v share their other endpoint). "
            f"For v = {ex.selected}: |L(v)| = {len(_vi(ex)['L'])}, one-to-one? "
            f"{_yn(_vi(ex)['inj'])}, so |N(v)| = deg v? {_yn(_vi(ex)['eq'])}."),
        lean=("`hN`: by `rw [image_otherEnd]`, |N(v)| is the size of the image. `hle` "
              "(`Finset.card_image_le`): an image is never larger than its source. `hfull` "
              "(`Finset.card_image_iff`): the image has full size exactly when the map is "
              "one-to-one (`Set.InjOn`). `rw [hN, deg_eq, ← hfull]` turns the goal into "
              "arithmetic on three numbers N, I, L: N = I + L ↔ L = 0 ∧ N = I. `omega` solves "
              "that, using hle : N ≤ I."),
    ),
    dict(
        part=P4, title="Two directions: constructor", code="main",
        ranges=[("(∀ v : V, (G.nbrFinset v).card = G.deg v) ↔ G.IsSimple := by", "intro hEq")],
        focus="vertex",
        math=lambda ex, f: (
            "We prove each direction separately. (⇒) Assume |N(v)| = deg v at every vertex; "
            "show G has no loops and no multiple edges. (⇐) Assume G is simple; show |N(v)| = "
            "deg v at every vertex. " + _all_line(ex)),
        lean=("`constructor` splits the goal `A ↔ B` into two goals, `A → B` and `B → A`. Each "
              "`·` (bullet) starts the proof of one of them. `intro hEq` assumes A and names it: "
              "now `hEq : ∀ v, (G.nbrFinset v).card = G.deg v` is available, and the goal is "
              "`G.IsSimple`. Lines starting with `--` are comments for humans."),
    ),
    dict(
        part=P4, title="(⇒) No loops", code="main",
        ranges=[("have hNoLoops : ∀ e : E, ¬ G.IsLoop e := by",
                 "exact absurd heL (Finset.notMem_empty e)")], focus="loop",
        math=lambda ex, f: (
            "Suppose some edge e were a loop, at a vertex a. Then e ∈ L(a), so L(a) is not "
            "empty. But |N(a)| = deg a, and the key lemma says that forces L(a) = ∅. "
            "Contradiction: there is no loop. " + _loop_witness_text(ex, f)),
        lean=("`¬ P` means 'P → False', so `intro e hloop` takes an edge e and hloop : e is a "
              "loop; the goal is False. `obtain ⟨a, ha⟩` finds a with ends e = s(a, a); its "
              "proof uses `induction … using Sym2.ind` (treat each s(x, y)) and "
              "`Sym2.mk_isDiag_iff` (s(x, y) is diagonal ↔ x = y). `heL : e ∈ loopsAt G a` by "
              "simp only. `hL0` is part `.1` of the key lemma applied (`.mp`) to `hEq a`. "
              "`rw [Finset.card_eq_zero] at hL0` makes it L(a) = ∅, `rw [hL0] at heL` gives "
              "e ∈ ∅, and `absurd heL (Finset.notMem_empty e)` uses e ∈ ∅ and e ∉ ∅."),
    ),
    dict(
        part=P4, title="(⇒) No multiple edges, so G is simple", code="main",
        ranges=[("have hNoMultiple : ¬ G.HasMultipleEdges := by",
                 "exact ⟨hNoMultiple, hNoLoops⟩")], focus="multi",
        math=lambda ex, f: (
            "Suppose two different edges e₁, e₂ had the same endpoints {a, b}. Both are "
            "incident with a and both have other endpoint b, so the map at a is not "
            "one-to-one. But |N(a)| = deg a forces it to be one-to-one (key lemma). "
            "Contradiction. No loops and no multiple edges: G is simple. "
            + _multi_witness_text(ex, f)),
        lean=("`rintro ⟨e₁, e₂, hne, hsame⟩` assumes HasMultipleEdges and unpacks it (hne : "
              "e₁ ≠ e₂). `obtain ⟨a, b, hab⟩` names the endpoints (again via Sym2.ind). "
              "`hsame.symm.trans hab` chains ends e₂ = ends e₁ = s(a, b). `hinc`: any edge on "
              "{a, b} is in I(a). `hsameOther` rewrites both other endpoints to b (Fact 2). "
              "`hInj` is part `.2` of the key lemma. `hInj (…) (…) hsameOther : e₁ = e₂`, and "
              "`hne` of that is False. `exact ⟨hNoMultiple, hNoLoops⟩` builds IsSimple."),
    ),
    dict(
        part=P4, title="(⇐) Set-up: reduce to the key lemma", code="main",
        ranges=[("· -- (⇐) in a simple graph", "constructor")], focus="vertex",
        math=lambda ex, f: (
            "Now assume G is simple and take any vertex v. By the key lemma it is enough to "
            "show (1) there is no loop at v, and (2) the map at v is one-to-one. "
            f"For v = {ex.selected}: |L(v)| = {len(_vi(ex)['L'])}, one-to-one? "
            f"{_yn(_vi(ex)['inj'])}" + (" (this graph is simple)." if is_simple(ex.ends) else
                                         " (this graph is not simple, so (⇐) does not apply "
                                         "to it).")),
        lean=("`rintro ⟨hNoMultiple, hNoLoops⟩ v` unpacks 'G is simple' into its two parts and "
              "takes an arbitrary vertex v (the goal was ∀ v, …). `rw [card_nbr_eq_deg_iff]` "
              "replaces the goal |N(v)| = deg v by the equivalent |L(v)| = 0 ∧ InjOn …, using "
              "the ↔ of the key lemma. `constructor` splits the ∧ into two goals."),
    ),
    dict(
        part=P4, title="(⇐) No loops at v", code="main",
        ranges=[("· -- no loops at `v`", "exact Sym2.mk_isDiag_iff.mpr rfl")], focus="vertex",
        math=lambda ex, f: (
            "If some edge e were in L(v), then e = {v}: a loop. A simple graph has none, so "
            f"L(v) is empty and |L(v)| = 0. For v = {ex.selected} here: L(v) = "
            f"{fmt_edges(_vi(ex)['L'])}."),
        lean=("`rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]` turns |L(v)| = 0 "
              "into L(v) = ∅ and then into ∀ e, e ∉ L(v). `intro e he` takes e with he : e ∈ L(v)"
              "; the goal is False. `simp only […] at he` unfolds he to G.ends e = s(v, v). "
              "`apply hNoLoops e`: since ¬IsLoop e means IsLoop e → False, it remains to prove "
              "IsLoop e. `rw [UGraph.IsLoop, he]` makes that s(v, v).IsDiag, and "
              "`Sym2.mk_isDiag_iff.mpr rfl` proves it from v = v."),
    ),
    dict(
        part=P4, title="(⇐) One-to-one at v  ∎", code="main",
        ranges=[("· -- two incident edges with the same other endpoint",
                 "exact hNoMultiple ⟨e₁, e₂, hne, hsameEnds⟩")], focus="vertex",
        math=lambda ex, f: (
            "Take two edges e₁, e₂ at v with the same other endpoint u. By Fact 1 both have "
            "endpoints {v, u}. If they were different edges they would be multiple edges, "
            "impossible in a simple graph. So e₁ = e₂: the map is one-to-one, and by the key "
            "lemma |N(v)| = deg v. ∎  "
            + (f"Here at v = {ex.selected} the map is one-to-one ✓." if _vi(ex)["inj"] else
               f"Here at v = {ex.selected} two edges share an endpoint, which is only possible "
               "because this graph is not simple.")),
        lean=("`intro e₁ h₁ e₂ h₂ hsameOther` unpacks Set.InjOn: two edges, proofs that they "
              "lie in I(v), and equal other endpoints; the goal is e₁ = e₂. `simp only … at h₁ h₂` "
              "turns membership in the filtered set into G.Incident. `hsameEnds` rewrites both "
              "ends with Fact 1 and then uses hsameOther. `by_contra hne` assumes e₁ ≠ e₂ and "
              "asks for False; `hNoMultiple ⟨e₁, e₂, hne, hsameEnds⟩` supplies exactly the "
              "forbidden multiple edges."),
    ),
    dict(
        part=P5, title="Examples are evidence; the Lean proof is the proof", code="main",
        anchors=[], focus="vertex",
        math=lambda ex, f: (
            "Each picture is ONE graph. The script also checked every graph with at most 4 "
            f"vertices and at most 4 edges ({ex.stats['n_graphs']:,} graphs, loops and multiple "
            "edges allowed): |N(v)| = deg v at every v exactly when the graph is simple, and "
            "every lemma holds at every vertex. That is evidence, not a proof: it says nothing "
            "about larger graphs. The Lean proof covers every finite graph, because each step "
            "is a general argument."),
        lean=("`#print axioms GraphCh10.supp10b` lists only Lean's three standard axioms "
              "(propext, Classical.choice, Quot.sound), basic logical principles almost every "
              "Lean proof relies on. There is no `sorry` (unfinished step) and no axiom added by "
              "the project. Lean's kernel has checked every step shown above."),
    ),
]


# ---------------------------------------------------------------------------
# 8. The interactive explorer
# ---------------------------------------------------------------------------

class Explorer:
    """Interactive companion: choose v, edit loops / parallel edges, step through the proof."""

    MAX_CODE_LINES = 32

    def __init__(self, stats: dict):
        self.stats = stats
        self.lean = read_lean_sources()
        self._check_anchors()
        self.example = START_EXAMPLE
        self.ends: Ends = dict(EXAMPLES[START_EXAMPLE][1])
        self.selected = START_V
        self.step = 0
        self.message = ""
        self.graph_labels: list = []

        for key in ("keymap.back", "keymap.forward"):  # free ← / → for the walkthrough
            plt.rcParams[key] = [k for k in plt.rcParams[key] if k not in ("left", "right")]

        self.fig = plt.figure(figsize=(18, 11.5), facecolor="white")
        try:
            self.fig.canvas.manager.set_window_title("Supp. 10(b): |N(v)| = deg v ⇔ simple")
        except AttributeError:
            pass
        self.fig.text(0.015, 0.972, "Supplementary Exercise 10(b):  |N(v)| = deg v for every v"
                      "  ⇔  G is simple", fontsize=18, fontweight="bold", color=COLOR_TEXT,
                      va="center")
        self.fig.text(0.015, 0.942, "An interactive companion to the Lean proof GraphCh10.supp10b."
                      " Every picture is one example; the Lean proof covers every finite graph.",
                      fontsize=10.5, color=COLOR_WARN, style="italic", va="center")
        self.fig.text(0.015, 0.913, "Click a vertex to choose v.  Buttons below: switch "
                      "examples, add/remove a loop or parallel edge at v.", fontsize=9.8,
                      color="#444444", va="center")

        self.caption = self.fig.text(0.015, 0.888, "", ha="left", va="top", fontsize=10,
                                     color=COLOR_TEXT, linespacing=1.4)
        self.ax_graph = self.fig.add_axes([0.005, 0.36, 0.27, 0.47])
        self.ax_map = self.fig.add_axes([0.28, 0.36, 0.21, 0.47])
        self.ax_legend = self.fig.add_axes([0.015, 0.295, 0.475, 0.06])
        self.ax_counts = self.fig.add_axes([0.015, 0.175, 0.475, 0.115])
        self.ax_text = self.fig.add_axes([0.51, 0.6, 0.475, 0.33])
        self.ax_code = self.fig.add_axes([0.51, 0.105, 0.475, 0.48])
        for ax in (self.ax_legend, self.ax_counts, self.ax_text, self.ax_code):
            ax.axis("off")

        def button(rect, label, cb, color="#F0F0F0", size=10):
            b = Button(self.fig.add_axes(rect), label, color=color, hovercolor="#DDE8F5")
            b.label.set_fontsize(size)
            b.on_clicked(cb)
            return b

        self.fig.text(0.015, 0.14, "Example:", fontsize=10, fontweight="bold", va="center")
        self.fig.text(0.015, 0.09, "Edit at v:", fontsize=10, fontweight="bold", va="center")
        x0, w, gap = 0.085, 0.0925, 0.0075
        labels = {"simple": "Simple", "loop": "Loop", "parallel": "Parallel",
                  "both": "Loop + parallel"}
        self.btn_examples = {}
        for k, key in enumerate(EXAMPLE_ORDER):
            self.btn_examples[key] = button([x0 + k * (w + gap), 0.122, w, 0.036], labels[key],
                                            lambda _e, key=key: self.set_example(key))
        self.btn_add_loop = button([x0, 0.072, w, 0.036], "+ loop at v",
                                   lambda _e: self.edit("add_loop"), color="#F7E6E6")
        self.btn_del_loop = button([x0 + (w + gap), 0.072, w, 0.036], "− loop at v",
                                   lambda _e: self.edit("del_loop"), color="#E3EEDF")
        self.btn_add_par = button([x0 + 2 * (w + gap), 0.072, w, 0.036], "+ parallel at v",
                                  lambda _e: self.edit("add_par"), color="#F7E6E6")
        self.btn_del_par = button([x0 + 3 * (w + gap), 0.072, w, 0.036], "− parallel at v",
                                  lambda _e: self.edit("del_par"), color="#E3EEDF")
        self.btn_reset = button([x0, 0.022, w, 0.036], "Reset", lambda _e: self.reset(),
                                color="#E3EEDF")
        self.status = self.fig.text(x0 + w + gap, 0.04, "", fontsize=9.5, va="center",
                                    color="#444444", style="italic")

        self.btn_prev = button([0.51, 0.035, 0.09, 0.055], "◀ Previous", lambda _e: self.go(-1),
                               size=10.5)
        self.btn_next = button([0.72, 0.035, 0.09, 0.055], "Next ▶", lambda _e: self.go(+1),
                               color="#E3EEDF", size=10.5)
        self.step_label = self.fig.text(0.66, 0.0625, "", ha="center", va="center",
                                        fontsize=11, fontweight="bold", color=COLOR_TEXT)
        self.fig.text(0.985, 0.0625, "keys: ← / →", ha="right", va="center", fontsize=9.5,
                      color="#777777")

        self.ax_legend.legend(handles=legend_handles(), loc="center", ncol=4, frameon=False,
                              fontsize=9.5, handlelength=2.2, columnspacing=1.3)
        self.fig.canvas.mpl_connect("button_press_event", self._on_click)
        self.fig.canvas.mpl_connect("key_press_event", self._on_key)
        self.enter_step(0)

    # -- state --------------------------------------------------------------

    def _check_anchors(self) -> None:
        """Every anchor and range start matches exactly one line; every range end exists."""
        for s in STEPS:
            lines = self.lean[s["code"]]
            for sub in list(s.get("anchors", [])) + [a for a, _b in s.get("ranges", [])]:
                n = sum(sub in ln for ln in lines)
                assert n == 1, f"anchor {sub!r} matches {n} lines of the {s['code']} source"
            self.highlighted(s)

    def highlighted(self, s: dict) -> list[int]:
        """Indices of the source lines a step highlights."""
        lines = self.lean[s["code"]]
        idx = {i for a in s.get("anchors", []) for i, ln in enumerate(lines) if a in ln}
        for a, b in s.get("ranges", []):
            i = next(i for i, ln in enumerate(lines) if a in ln)
            j = next((j for j in range(i, len(lines)) if b in lines[j]), None)
            assert j is not None, f"range end {b!r} not found after {a!r}"
            idx |= set(range(i, j + 1))
        return sorted(idx)

    @property
    def vs(self) -> list[int]:
        return list(range(N_V))

    @property
    def edited(self) -> bool:
        return self.ends != EXAMPLES[self.example][1]

    def _fresh_name(self) -> str:
        return f"e{max((int(e[1:]) for e in self.ends), default=-1) + 1}"

    def set_example(self, key: str) -> None:
        self.example, self.ends = key, dict(EXAMPLES[key][1])
        self.selected, self.message = START_V, f"switched to: {EXAMPLES[key][0]}"
        self._auto_select()
        self.redraw()

    def reset(self) -> None:
        self.ends, self.selected = dict(EXAMPLES[self.example][1]), START_V
        self.message = "reset"
        self._auto_select()
        self.redraw()

    def edit(self, kind: str) -> None:
        """Add or remove a loop or a parallel edge at the chosen vertex v."""
        v, ends = self.selected, dict(self.ends)
        loops = loops_at(ends, v)
        if kind == "add_loop":
            if len(loops) >= MAX_LOOPS_AT_V:
                self.message = f"at most {MAX_LOOPS_AT_V} loops at a vertex here"
                return self.redraw()
            e = self._fresh_name()
            ends[e] = frozenset({v})
            msg = f"added loop {e} at {v}"
        elif kind == "del_loop":
            if not loops:
                self.message = f"no loop at {v} to remove"
                return self.redraw()
            e = loops[-1]
            del ends[e]
            msg = f"removed loop {e} at {v}"
        elif kind == "add_par":
            targets = [u for u in self.vs if u != v and adj(ends, v, u) and
                       sum(s == frozenset({v, u}) for s in ends.values()) < MAX_COPIES]
            if not targets:
                self.message = f"no edge at {v} to copy (or {MAX_COPIES} copies already)"
                return self.redraw()
            u = targets[0]
            e = self._fresh_name()
            ends[e] = frozenset({v, u})
            msg = f"added {e} = {{{min(u, v)}, {max(u, v)}}}, parallel to an existing edge"
        elif kind == "del_par":
            groups = [[e for e in names(ends) if ends[e] == frozenset({v, u})]
                      for u in self.vs if u != v]
            groups = [g for g in groups if len(g) > 1]
            if not groups:
                self.message = f"no parallel edges at {v} to remove"
                return self.redraw()
            e = groups[0][-1]
            msg = f"removed {e} = {fmt_set(ends[e])}"
            del ends[e]
        else:
            raise ValueError(kind)
        self.ends, self.message = ends, msg
        self.redraw()

    def go(self, delta: int) -> None:
        self.enter_step(max(0, min(len(STEPS) - 1, self.step + delta)))

    def enter_step(self, k: int) -> None:
        self.step = k
        self._auto_select()
        self.redraw()

    def _auto_select(self) -> None:
        """On the (⇒) steps, choose v = the vertex a of the loop / parallel edges, if any."""
        kind = STEPS[self.step]["focus"]
        if kind in ("loop", "multi"):
            f = self.focus_info(kind)
            if f.get("a") is not None:
                self.selected = f["a"]

    def select_vertex(self, v: int) -> None:
        self.selected = v
        self.message = ""
        self.redraw()

    # -- events -------------------------------------------------------------

    def _on_click(self, event) -> None:
        if event.inaxes is not self.ax_graph or event.button != 1 or event.xdata is None:
            return
        pos = positions(N_V)
        x, y = event.xdata, event.ydata
        v = min(self.vs, key=lambda w: (pos[w][0] - x) ** 2 + (pos[w][1] - y) ** 2)
        if (pos[v][0] - x) ** 2 + (pos[v][1] - y) ** 2 <= (1.6 * NODE_R) ** 2:
            self.select_vertex(v)

    def _on_key(self, event) -> None:
        if event.key == "right":
            self.go(+1)
        elif event.key == "left":
            self.go(-1)

    # -- what to highlight --------------------------------------------------

    def focus_info(self, kind: str | None) -> dict:
        """What the graph highlights for the current step."""
        v, ends, vs = self.selected, self.ends, self.vs
        info = vinfo(ends, v, vs)
        base = dict(edges=v_colors(ends, v), emph=frozenset(), tags={v: "v"},
                    rings=frozenset(info["N"]), caption=_counts(self))
        if kind in (None, "vertex", "incident"):
            return base
        if kind == "nbrs":
            return dict(base, tags={**{u: "nbr" for u in info["N"] if u != v}, v: "v"})
        if kind == "offenders":
            oc = offender_colors(ends)
            return dict(base, edges=oc, emph=frozenset(oc), tags={}, rings=frozenset(),
                        caption=_offenders(self) + f";  simple? {_yn(is_simple(ends))}")
        if kind == "loop":
            loops = [e for e in names(ends) if is_loop(ends, e)]
            if not loops:
                return dict(base, e=None, a=None, caption="no loop in this graph")
            here = [e for e in loops if v in ends[e]]
            e = (here or loops)[0]
            (a,) = tuple(ends[e])
            return dict(base, e=e, a=a, edges={**v_colors(ends, v), e: COLOR_FOCUS},
                        emph=frozenset({e}), tags={a: "a"},
                        caption=f"the loop {e} = {{{a}}}: {e} ∈ L({a})")
        if kind == "multi":
            pairs = multiple_edge_pairs(ends)
            pairs.sort(key=lambda p: (is_loop(ends, p[0]), v not in ends[p[0]]))
            if not pairs:
                return dict(base, pair=None, a=None, caption="no multiple edges in this graph")
            e1, e2 = pairs[0]
            s = ends[e1]
            a = v if v in s else min(s)
            b = other_end(ends, a, e1)
            tags = {a: "a"} if a == b else {a: "a", b: "b"}
            return dict(base, pair=(e1, e2), a=a, b=b,
                        edges={**v_colors(ends, v), e1: COLOR_FOCUS, e2: COLOR_FOCUS},
                        emph=frozenset({e1, e2}), tags=tags,
                        caption=f"{e1} ≠ {e2}, both with ends {fmt_set(s)}: otherEnd {a} {e1} "
                                f"= otherEnd {a} {e2} = {b}")
        raise ValueError(kind)

    # -- drawing ------------------------------------------------------------

    def redraw(self) -> None:
        s = STEPS[self.step]
        focus = self.focus_info(s["focus"])
        self._draw_graph(focus)
        draw_map(self.ax_map, self.ends, self.selected, self.vs)
        self._draw_counts()
        self._draw_text(s, focus)
        self._draw_code(s)
        last = len(STEPS) - 1
        self.step_label.set_text(f"Step {self.step + 1} / {len(STEPS)}"
                                 + ("  (end)" if self.step == last else ""))
        for b, off, on_color in ((self.btn_prev, self.step == 0, "#F0F0F0"),
                                 (self.btn_next, self.step == last, "#E3EEDF")):
            b.label.set_alpha(0.3 if off else 1.0)
            b.color = "#F7F7F7" if off else on_color
            b.ax.set_facecolor(b.color)
        for key, b in self.btn_examples.items():
            b.color = "#CFE0F5" if key == self.example else "#F0F0F0"
            b.ax.set_facecolor(b.color)
            b.label.set_fontweight("bold" if key == self.example else "normal")
        self.status.set_text(self.message)
        self.fig.canvas.draw_idle()

    def _draw_graph(self, focus: dict) -> None:
        ax = self.ax_graph
        ax.clear()
        head = EXAMPLES[self.example][0] + (" (edited)" if self.edited else "")
        head += f"   ·   simple? {_yn(is_simple(self.ends))}   ·   chosen vertex v = {self.selected}"
        self.graph_labels = draw_graph(ax, self.ends, self.vs, focus["edges"], focus["emph"],
                                       focus["tags"], focus["rings"], chosen=self.selected)
        frame(ax)
        self.caption.set_text(head + "\n" + textwrap.fill(focus["caption"], 105))

    def _draw_counts(self) -> None:
        """One chip per vertex with |N(v)| and deg v, then the two sides of the ↔."""
        ax = self.ax_counts
        ax.clear()
        ax.axis("off")
        ax.add_patch(plt.Rectangle((0, 0), 1, 1, transform=ax.transAxes, facecolor="#F7F7F7",
                                   edgecolor="#D0D0D0"))
        ax.text(0.015, 0.89, "Every vertex (the '∀ v' in the theorem):", transform=ax.transAxes,
                fontsize=10, fontweight="bold", va="top")
        cw = 0.112
        for j, w in enumerate(self.vs):
            i = vinfo(self.ends, w, self.vs)
            x = 0.015 + j * cw
            ok = i["eq"]
            col, bg = (COLOR_NBR, "#E8F5EC") if ok else (COLOR_WARN, "#FBE3E3")
            ax.add_patch(FancyBboxPatch((x + 0.004, 0.08), cw - 0.012, 0.56,
                                        boxstyle="round,pad=0.005,rounding_size=0.02",
                                        transform=ax.transAxes, facecolor=bg, edgecolor=col,
                                        linewidth=2.4 if w == self.selected else 1.2))
            ax.text(x + cw / 2 - 0.002, 0.52, f"v = {w}", transform=ax.transAxes, ha="center",
                    va="center", fontsize=9.5, fontweight="bold")
            ax.text(x + cw / 2 - 0.002, 0.33, f"{len(i['N'])} {'=' if ok else '≠'} {i['deg']}",
                    transform=ax.transAxes, ha="center", va="center", fontsize=10.5,
                    fontweight="bold", color=col)
            ax.text(x + cw / 2 - 0.002, 0.16, "|N| vs deg", transform=ax.transAxes,
                    ha="center", va="center", fontsize=8, color="#555555")
        all_eq = all(vinfo(self.ends, w, self.vs)["eq"] for w in self.vs)
        simple = is_simple(self.ends)
        x = 0.015 + N_V * cw + 0.015
        ax.text(x, 0.6, f"all equal?  {_yn(all_eq)}", transform=ax.transAxes, fontsize=10.5,
                fontweight="bold", va="center", color=COLOR_NBR if all_eq else COLOR_WARN)
        ax.text(x, 0.42, f"simple?     {_yn(simple)}", transform=ax.transAxes, fontsize=10.5,
                fontweight="bold", va="center", color=COLOR_NBR if simple else COLOR_WARN)
        ax.text(x, 0.2, "same answer ✓ (the ↔)" if all_eq == simple else "MISMATCH ✗",
                transform=ax.transAxes, fontsize=9.5, va="center", color="#444444")

    def _draw_text(self, s: dict, focus: dict) -> None:
        ax = self.ax_text
        ax.clear()
        ax.axis("off")
        blocks = [("Graph theory idea", s["math"](self, focus).replace("`", "")),
                  ("Lean syntax", s["lean"].replace("`", ""))]
        height_pt = ax.get_position().height * self.fig.get_figheight() * 72
        width_in = ax.get_position().width * self.fig.get_figwidth()
        for size in (11, 10.5, 10, 9.5, 9, 8.5, 8, 7.5):
            width = int(width_in * 72 / (size * 0.56))
            wrapped = [(h, [ln for para in t.split("\n")
                            for ln in textwrap.wrap(para, width, subsequent_indent=(
                                "  " if para.startswith("•") else ""))])
                       for h, t in blocks]
            n_lines = 1.3 + 1.9 + sum(1.25 + len(w) + 0.6 for _h, w in wrapped)
            if n_lines * size * 1.4 <= height_pt:
                break
        self.text_fontsize = size
        line = size * 1.4 / height_pt
        y = 1.0
        ax.text(0, y, s["part"].upper(), transform=ax.transAxes, fontsize=size - 0.5,
                color="#777777", va="top", fontweight="bold")
        y -= 1.3 * line
        ax.text(0, y, s["title"], transform=ax.transAxes, fontsize=size + 4, va="top",
                fontweight="bold", color=COLOR_TEXT)
        y -= 1.9 * line
        for head, lines in wrapped:
            ax.text(0, y, head, transform=ax.transAxes, fontsize=size, va="top",
                    fontweight="bold",
                    color=COLOR_NBR if head == "Lean syntax" else COLOR_VERTEX)
            y -= 1.25 * line
            ax.text(0, y, "\n".join(lines), transform=ax.transAxes, fontsize=size, va="top",
                    color=COLOR_TEXT, linespacing=1.4)
            y -= (len(lines) + 0.6) * line

    def code_window(self, s: dict) -> tuple[int, int]:
        """The slice of the source shown: everything if it fits, else a window containing all
        highlighted lines (centred on them)."""
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
        step_y = 0.9 / n
        fontsize = 8.6 if n <= 28 else 7.9
        for r, (i, ln) in enumerate(rows):
            is_hl = i is not None and i in hl
            y = 0.93 - r * step_y
            if is_hl:
                ax.add_patch(plt.Rectangle((0.008, y - step_y * 0.95), 0.984, step_y * 0.98,
                                           transform=ax.transAxes, facecolor=COLOR_CODE_HL,
                                           edgecolor=COLOR_FOCUS, linewidth=1))
            comment = ln.strip().startswith(("--", "/--", "-/")) or i is None
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


def _key(ex: Explorer, key: str) -> None:
    ex.fig.canvas.callbacks.process("key_press_event",
                                    KeyEvent("key_press_event", ex.fig.canvas, key))


def _overlaps(texts, renderer, pad: float = 1.0) -> list[tuple[str, str]]:
    boxes = [(t.get_text(), t.get_window_extent(renderer)) for t in texts
             if t.get_visible() and t.get_text().strip()]
    bad = []
    for (s1, b1), (s2, b2) in combinations(boxes, 2):
        if (b1.x0 + pad < b2.x1 and b2.x0 + pad < b1.x1 and
                b1.y0 + pad < b2.y1 and b2.y0 + pad < b1.y1):
            bad.append((s1, s2))
    return bad


def _check_layout(ex: Explorer) -> None:
    """No text runs out of its panel; no two texts overlap in the map, counts and graph."""
    ex.fig.canvas.draw()
    renderer = ex.fig.canvas.get_renderer()
    for ax in (ex.ax_text, ex.ax_code, ex.ax_map, ex.ax_counts, ex.ax_graph):
        box = ax.get_window_extent(renderer)
        for t in ax.texts:
            if not t.get_text().strip():
                continue
            bb = t.get_window_extent(renderer)
            assert (bb.y0 >= box.y0 - 2 and bb.x1 <= box.x1 + 2 and bb.x0 >= box.x0 - 2
                    and bb.y1 <= box.y1 + 2), f"text overflows its panel: {t.get_text()[:60]!r}"
    for ax in (ex.ax_map, ex.ax_counts):
        bad = _overlaps(ax.texts, renderer)
        assert not bad, f"overlapping texts: {bad[:3]}"
    bad = _overlaps(ex.graph_labels, renderer)
    assert not bad, f"overlapping graph labels: {bad[:3]}"
    # The caption above the graph stays above the graph's drawn content.
    cb = ex.caption.get_window_extent(renderer)
    assert cb.x1 <= ex.ax_text.get_window_extent(renderer).x0, "caption runs into the text"


def _nums(ex: Explorer, v: int) -> tuple[int, int, int, int]:
    i = vinfo(ex.ends, v, ex.vs)
    return len(i["N"]), len(i["I"]), len(i["L"]), i["deg"]


def self_test(ex: Explorer, outdir: Path) -> None:
    outdir.mkdir(parents=True, exist_ok=True)
    pos = positions(N_V)
    # 1. Every step renders, on every example, with text and code fitting.
    for k, s in enumerate(STEPS):
        for key in EXAMPLE_ORDER:
            ex.set_example(key)
            ex.enter_step(k)
            _check_layout(ex)
        ex.set_example(START_EXAMPLE)
        ex.enter_step(k)
        a, b = ex.code_window(s)
        assert all(a <= i < b for i in ex.highlighted(s)), f"step {k + 1}: highlight off-screen"
        assert ex.highlighted(s) or s["part"] == P5, f"step {k + 1}: nothing highlighted"
        ex.message = ""
        ex.redraw()
        ex.fig.savefig(outdir / f"step_{k + 1:02d}.png", dpi=90)
    # 2. Next / Previous buttons and the arrow keys.
    ex.enter_step(0)
    _click(ex, ex.btn_next)
    assert ex.step == 1, "Next button did not advance"
    _click(ex, ex.btn_prev)
    assert ex.step == 0, "Previous button did not go back"
    _click(ex, ex.btn_prev)
    assert ex.step == 0, "Previous on the first step must stay there"
    _key(ex, "right")
    _key(ex, "right")
    assert ex.step == 2, "→ key did not advance"
    _key(ex, "left")
    assert ex.step == 1, "← key did not go back"
    ex.enter_step(len(STEPS) - 1)
    _click(ex, ex.btn_next)
    assert ex.step == len(STEPS) - 1, "Next on the last step must stay there"
    # 3. Example buttons: the computed numbers at v = 1 are the expected ones.
    ex.enter_step(5)  # the map step
    expect = {"simple": (3, 3, 0, 3), "loop": (4, 4, 1, 5), "parallel": (3, 4, 0, 4),
              "both": (4, 5, 1, 6)}  # (|N(1)|, |I(1)|, |L(1)|, deg 1)
    for key in EXAMPLE_ORDER:
        _click(ex, ex.btn_examples[key])
        assert ex.example == key and ex.ends == EXAMPLES[key][1] and ex.selected == START_V
        assert _nums(ex, START_V) == expect[key], (key, _nums(ex, START_V))
        assert is_simple(ex.ends) == (key == "simple")
        ex.fig.savefig(outdir / f"example_{key}.png", dpi=90)
    # 4. Clicking a vertex chooses v; clicking empty space changes nothing.
    for v in ex.vs:
        _press(ex.fig, ex.ax_graph, *pos[v])
        assert ex.selected == v, f"click on vertex {v} did not select it"
    _press(ex.fig, ex.ax_graph, *pos[3])
    ex.fig.savefig(outdir / "click_vertex_3.png", dpi=90)
    _press(ex.fig, ex.ax_graph, 0.0, 0.0)
    assert ex.selected == 3, "a click away from vertices must not change v"
    # 5. Editing on the simple graph: a loop adds 2 to deg but 1 neighbour; a parallel edge
    #    adds 1 to deg and no neighbour; removing them restores equality.
    _click(ex, ex.btn_examples["simple"])
    v = ex.selected
    n0, i0, l0, d0 = _nums(ex, v)
    assert n0 == d0 and is_simple(ex.ends)
    _click(ex, ex.btn_add_loop)
    n1, i1, l1, d1 = _nums(ex, v)
    assert (d1, n1, l1) == (d0 + 2, n0 + 1, 1) and not is_simple(ex.ends)
    ex.fig.savefig(outdir / "edit_add_loop.png", dpi=90)
    _click(ex, ex.btn_add_loop)  # a second loop: deg +2, no new neighbour (v already is one)
    assert _nums(ex, v)[3] == d0 + 4 and _nums(ex, v)[0] == n0 + 1
    _check_layout(ex)
    ex.fig.savefig(outdir / "edit_two_loops.png", dpi=90)
    _click(ex, ex.btn_del_loop)
    _click(ex, ex.btn_del_loop)
    assert _nums(ex, v) == (n0, i0, l0, d0) and is_simple(ex.ends)
    _click(ex, ex.btn_del_loop)  # nothing to remove: no change
    assert _nums(ex, v) == (n0, i0, l0, d0)
    _click(ex, ex.btn_add_par)
    n2, i2, _l2, d2 = _nums(ex, v)
    assert (d2, n2, i2) == (d0 + 1, n0, i0 + 1) and not is_simple(ex.ends)
    assert vinfo(ex.ends, v, ex.vs)["col"], "the parallel edge must collide in the map"
    ex.fig.savefig(outdir / "edit_add_parallel.png", dpi=90)
    for _ in range(4):  # up to MAX_COPIES copies per pair, then the next neighbour
        _click(ex, ex.btn_add_par)
    _click(ex, ex.btn_add_loop)
    _click(ex, ex.btn_add_loop)
    _check_layout(ex)
    ex.fig.savefig(outdir / "edit_crowded.png", dpi=90)
    for _ in range(8):
        _click(ex, ex.btn_del_par)
        _click(ex, ex.btn_del_loop)
    assert ex.ends == EXAMPLES["simple"][1], "removing everything added must restore the graph"
    _click(ex, ex.btn_add_par)
    _click(ex, ex.btn_reset)
    assert ex.ends == EXAMPLES["simple"][1] and ex.selected == START_V and not ex.edited
    # 6. Every vertex of every edited graph agrees with the theorem.
    assert all(vinfo(ex.ends, w, ex.vs)["eq"] for w in ex.vs) == is_simple(ex.ends)
    # 7. The (⇒) steps pick the vertex a of the loop / of the parallel edges.
    loop_step = next(i for i, s in enumerate(STEPS) if s["focus"] == "loop")
    multi_step = next(i for i, s in enumerate(STEPS) if s["focus"] == "multi")
    _click(ex, ex.btn_examples["loop"])
    ex.enter_step(loop_step)
    f = ex.focus_info("loop")
    assert f["e"] == "e6" and f["a"] == 1 == ex.selected and _vi(ex)["L"] == ["e6"]
    ex.fig.savefig(outdir / "witness_loop.png", dpi=90)
    _click(ex, ex.btn_examples["parallel"])
    ex.enter_step(multi_step)
    f = ex.focus_info("multi")
    assert f["pair"] == ("e1", "e6") and f["a"] == 1 and f["b"] == 2
    assert _vi(ex)["col"] == {2: ["e1", "e6"]}
    ex.fig.savefig(outdir / "witness_parallel.png", dpi=90)
    _click(ex, ex.btn_examples["simple"])
    assert ex.focus_info("multi")["pair"] is None
    _check_layout(ex)
    print(f"Explorer self-test passed: {len(STEPS)} steps rendered on all 4 examples (text, "
          f"code, map and labels fit without overlap); buttons, keys, vertex clicks, example "
          f"switching, add/remove loop and parallel edge, and reset work; snapshots in {outdir}")


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
                        help="headless self-test of the explorer; save PNGs into DIR")
    args = parser.parse_args()

    stats = run_checks()
    vs = list(range(N_V))
    for key in EXAMPLE_ORDER:
        label, ends = EXAMPLES[key]
        print(f"{label:28s} simple={_yn(is_simple(ends)):3s}  |N(v)|/deg v: " +
              ", ".join(f"{v}:{len(nbr_finset(ends, v, vs))}/{deg(ends, v)}" for v in vs))
    print(f"All assertions passed (approved statement, examples, and every lemma of Supp10b.lean "
          f"on all {stats['n_graphs']:,} graphs with ≤ 4 vertices and ≤ 4 edges, "
          f"{stats['n_simple']:,} of them simple). This is evidence; the Lean proof is the proof.")

    out = Path(__file__).resolve().parent / "supp10b.png"
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
