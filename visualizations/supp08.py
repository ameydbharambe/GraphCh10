"""Visualization for Rosen Ch. 10, Supplementary Exercise 8 (a DISPROOF by counterexample).

    "Prove or disprove that there are always two vertices of the same degree in a finite
     multigraph having at least two vertices."

The statement is FALSE. An EDUCATIONAL COMPANION to the Lean theorem `GraphCh10.supp08`
(GraphCh10/Exercises/Supp08.lean), for students learning Lean 4 and introductory graph
theory. It has two parts:

1. A static summary figure (visualizations/supp08.png) of the counterexample.
2. An interactive explorer: click a vertex to see how its degree is counted, add or remove
   parallel edges (and a loop) to see how degrees change, and step through the actual Lean
   proof with Previous/Next. Each step explains the mathematics and the Lean tactic and
   highlights the matching vertices and edges. The Lean code shown is read from the project
   files at runtime.

Unlike Exercise 9(a), here ONE example really is the whole answer: to show that a
"for every multigraph ..." statement is false, a single multigraph that breaks it is enough.
The Lean proof checks exactly this graph.

The graph model follows GraphCh10/Definitions.lean exactly:

* `UGraph V E` -- vertices V, edges E, and `ends : E → Sym2 V`, the set {u, w} with one
  or two elements associated to each edge. Here `ends[e]` is a frozenset of size 1
  (a loop) or 2. Distinct edges may share the same ends (multiple / parallel edges).
* `IsLoop e := (G.ends e).IsDiag`            -- `is_loop(e)`: the set has one element.
* `IsMultigraph := ∀ e : E, ¬ G.IsLoop e`    -- `is_multigraph()`: no loops at all.
* `Incident e v := v ∈ G.ends e`             -- `incident(e, v)`.
* `deg v := #{e | Incident e v} + #{e | ends e = s(v, v)}`  -- `deg(v)`: loops count twice.

The counterexample is NOT typed in by hand: it is parsed from the definition of `ex8` in
GraphCh10/DefinitionTests.lean, the graph the Lean proof uses. Every degree is COMPUTED
from `ends` with the definition above; none is hardcoded.

Run (from the project root):
    python -m pip install networkx matplotlib
    python visualizations/supp08.py              # save the PNG, then open the explorer
    python visualizations/supp08.py --static     # only checks + PNG (no window)
    python visualizations/supp08.py --snapshots DIR
        # headless self-test: drives the explorer through every walkthrough step,
        # simulates mouse clicks, and saves one PNG per step into DIR

Every mode first runs the checks and re-saves visualizations/supp08.png.

Explorer controls:
    click a vertex          show how its degree is counted (its incident edges turn gold)
    − / +  buttons          remove / add a parallel copy of the edge {0,1}, {0,2} or {1,2}
    loop at 0 / 1 / 2       add or remove a loop at that vertex (then it is no longer a multigraph)
    Hide / Show degrees     hide every computed degree, predict them, then check
    Reset to ex8            restore the counterexample used by the Lean proof
    ◀ Previous / Next ▶     move through the walkthrough (also ← / → keys)
    Next example            show another vertex / pair for the current step
"""

from __future__ import annotations

import argparse
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
from matplotlib.patches import Circle, FancyArrowPatch, Patch
from matplotlib.widgets import Button

PROJECT_ROOT = Path(__file__).resolve().parent.parent
PROOF_FILE = PROJECT_ROOT / "GraphCh10" / "Exercises" / "Supp08.lean"
DEFS_FILE = PROJECT_ROOT / "GraphCh10" / "Definitions.lean"
TESTS_FILE = PROJECT_ROOT / "GraphCh10" / "DefinitionTests.lean"

# ---------------------------------------------------------------------------
# 1. The counterexample, parsed from the Lean definition of `ex8`
# ---------------------------------------------------------------------------

EX8_PATTERN = re.compile(
    r"^def ex8 : UGraph \(Fin (\d+)\) \(Fin (\d+)\) := "
    r"⟨fun e => if e = 0 then s\((\d+), (\d+)\) else s\((\d+), (\d+)\)⟩$")


def _require(path: Path) -> list[str]:
    if not path.exists():
        sys.exit(f"error: cannot find {path}; run this script inside the GraphCh10 project")
    return path.read_text(encoding="utf-8").splitlines()


def parse_ex8() -> tuple[list[int], dict[str, frozenset[int]], str]:
    """Read `def ex8` from DefinitionTests.lean and rebuild (V, ends) from it.

    `ex8 : UGraph (Fin n) (Fin m) := ⟨fun e => if e = 0 then s(a, b) else s(c, d)⟩` has
    vertices 0..n-1 and edges 0..m-1; edge 0 has ends {a, b}, every other edge {c, d}."""
    hits = [ln.strip() for ln in _require(TESTS_FILE) if ln.strip().startswith("def ex8")]
    assert len(hits) == 1, "expected exactly one `def ex8` in DefinitionTests.lean"
    m = EX8_PATTERN.match(hits[0])
    assert m, f"`def ex8` no longer has the expected shape:\n  {hits[0]}"
    n_v, n_e, a, b, c, d = map(int, m.groups())
    vertices = list(range(n_v))
    ends_map = {f"e{i}": (frozenset({a, b}) if i == 0 else frozenset({c, d}))
                for i in range(n_e)}
    return vertices, ends_map, hits[0]


V, EX8_ENDS, EX8_SOURCE = parse_ex8()


def edge_names(n: int) -> list[str]:
    """Edge i of `Fin n` is shown as e{i} (so `e = 0` in Lean is the edge e0)."""
    return [f"e{i}" for i in range(n)]


def as_map(ends_list: list[frozenset[int]]) -> dict[str, frozenset[int]]:
    return dict(zip(edge_names(len(ends_list)), ends_list))


# ---------------------------------------------------------------------------
# 2. The definitions, mirroring GraphCh10/Definitions.lean
# ---------------------------------------------------------------------------

def sym2(u: int, w: int) -> frozenset[int]:
    """s(u, w): the unordered pair {u, w} (a single element when u = w)."""
    return frozenset({u, w})


def is_loop(ends_map: dict, e: str) -> bool:
    """`IsLoop e := (G.ends e).IsDiag`: the associated set has a single element."""
    return len(ends_map[e]) == 1


def is_multigraph(ends_map: dict) -> bool:
    """`IsMultigraph := ∀ e : E, ¬ G.IsLoop e`."""
    return all(not is_loop(ends_map, e) for e in ends_map)


def incident(ends_map: dict, e: str, v: int) -> bool:
    """`Incident e v := v ∈ G.ends e`."""
    return v in ends_map[e]


def incident_edges(ends_map: dict, v: int) -> list[str]:
    """The edges counted by the first summand of `deg v`."""
    return [e for e in ends_map if incident(ends_map, e, v)]


def loops_at(ends_map: dict, v: int) -> list[str]:
    """The edges counted by the second summand of `deg v`: those with ends = s(v, v)."""
    return [e for e in ends_map if ends_map[e] == sym2(v, v)]


def deg(ends_map: dict, v: int) -> int:
    """`deg v := (univ.filter (Incident · v)).card + (univ.filter (ends · = s(v, v))).card`."""
    return len(incident_edges(ends_map, v)) + len(loops_at(ends_map, v))


def degrees(ends_map: dict) -> dict[int, int]:
    return {v: deg(ends_map, v) for v in V}


def equal_degree_pairs(ends_map: dict, vertices=None) -> list[tuple[int, int]]:
    """All pairs u < w with deg u = deg w: the witnesses the (false) claim asks for."""
    vs = V if vertices is None else vertices
    d = {v: deg(ends_map, v) for v in vs}
    return [(u, w) for u, w in combinations(vs, 2) if d[u] == d[w]]


def is_counterexample(ends_map: dict, vertices=None) -> bool:
    """A multigraph with ≥ 2 vertices in which no two distinct vertices share a degree."""
    vs = V if vertices is None else vertices
    return (is_multigraph(ends_map) and len(vs) >= 2
            and not equal_degree_pairs(ends_map, vs))


EX8_DEG = degrees(EX8_ENDS)
PAIRS = [(u, w) for u in V for w in V]  # the 9 cases of `match u, w with`, in order


# ---------------------------------------------------------------------------
# 3. Programmatic checks
# ---------------------------------------------------------------------------

def lean_degree_claims() -> dict[int, int]:
    """The degrees stated by `have hDeg : ex8.deg 0 = 1 ∧ ...` in Supp08.lean."""
    hits = [ln for ln in _require(PROOF_FILE) if "have hDeg" in ln]
    assert len(hits) == 1, "expected exactly one `have hDeg` line in Supp08.lean"
    claims = {int(v): int(k) for v, k in re.findall(r"ex8\.deg (\d+) = (\d+)", hits[0])}
    assert sorted(claims) == V, f"hDeg should state the degree of every vertex: {claims}"
    return claims


def multigraphs_on(vertices: list[int], max_mult: int):
    """Every loopless multigraph on `vertices` with at most `max_mult` copies of each pair."""
    pairs = list(combinations(vertices, 2))
    for mults in product(range(max_mult + 1), repeat=len(pairs)):
        yield [frozenset(p) for p, k in zip(pairs, mults) for _ in range(k)]


def run_checks() -> dict:
    """Assert every fact the picture and the walkthrough rely on. Returns summary numbers."""
    # Well-formedness of the UGraph model: every edge has a set of one or two vertices of V.
    assert all(1 <= len(s) <= 2 and s <= set(V) for s in EX8_ENDS.values())

    # The three hypotheses / conclusion of the claim, for ex8 (as in hMulti, hCard, hDistinct).
    assert is_multigraph(EX8_ENDS), "ex8 must have no loops"
    assert len(V) >= 2, "ex8 must have at least two vertices"
    assert equal_degree_pairs(EX8_ENDS) == [], "ex8 must have pairwise different degrees"
    assert is_counterexample(EX8_ENDS)

    # The degrees agree with what the Lean proof states in `hDeg`.
    assert EX8_DEG == lean_degree_claims(), f"{EX8_DEG} vs {lean_degree_claims()}"

    # ex8 really uses a parallel edge: two distinct edges with the same ends.
    parallel = [(e, f) for e, f in combinations(EX8_ENDS, 2) if EX8_ENDS[e] == EX8_ENDS[f]]
    assert parallel, "ex8 is expected to contain parallel edges"

    # Cross-check our `deg` against NetworkX's degree on the same multigraph.
    G = to_networkx(EX8_ENDS)
    assert all(G.degree(v) == EX8_DEG[v] for v in V), "NetworkX disagrees on a degree"

    # Every one of the 9 match cases: diagonal ones are excluded by u ≠ w, the rest differ.
    for u, w in PAIRS:
        assert (u == w) or EX8_DEG[u] != EX8_DEG[w]

    # Extra 1: in SIMPLE graphs (no parallel edges, no loops) the claim is TRUE -- checked
    # exhaustively for every simple graph on 2..5 vertices. So parallel edges are essential.
    n_simple = 0
    for n in range(2, 6):
        vs = list(range(n))
        for g in multigraphs_on(vs, 1):
            n_simple += 1
            assert equal_degree_pairs(as_map(g), vs), f"simple counterexample? {g}"

    # Extra 2: ex8 is as small as possible. On 2 vertices both degrees are always equal; on
    # 3 vertices every counterexample (≤ 3 copies of each pair) has at least 3 edges.
    for g in multigraphs_on([0, 1], 4):
        assert not is_counterexample(as_map(g), [0, 1])
    small = [g for g in multigraphs_on(V, 3) if is_counterexample(as_map(g))]
    assert small and min(len(g) for g in small) == len(EX8_ENDS) == 3
    assert sorted(EX8_ENDS.values(), key=sorted) in [sorted(g, key=sorted) for g in small]
    n_three = sum(1 for g in small if len(g) == 3)
    return dict(n_simple=n_simple, n_small=len(small), n_three=n_three)


def to_networkx(ends_map: dict) -> nx.MultiGraph:
    """The same graph as a NetworkX MultiGraph (edge keys are the edge names)."""
    G = nx.MultiGraph()
    G.add_nodes_from(V)
    for e, s in ends_map.items():
        endpoints = sorted(s)
        u, w = (endpoints * 2)[:2]  # a loop {v} becomes the pair (v, v)
        G.add_edge(u, w, key=e)
    return G


# ---------------------------------------------------------------------------
# 4. Shared drawing helpers
# ---------------------------------------------------------------------------

POS: dict[int, tuple[float, float]] = {0: (0.0, 0.0), 1: (2.0, 1.6), 2: (4.0, 0.0)}
BADGE_OFF: dict[int, tuple[float, float]] = {0: (0.0, -0.62), 1: (0.0, 0.64), 2: (0.0, -0.62)}
LOOP_DIR: dict[int, tuple[float, float]] = {0: (-1.0, 0.0), 1: (-0.98, 0.2), 2: (1.0, 0.0)}

COLOR_VERTEX = "#3B6FB6"   # blue vertex fill
COLOR_PARALLEL = "#E08A2C"  # orange: parallel edges (same ends as another edge)
COLOR_LOOP = "#9A2A2A"     # dark red: a loop (forbidden in a multigraph)
COLOR_OK = "#1E8C45"       # green: a check that holds
COLOR_FOCUS = "#F2B705"    # gold: the vertex / edges the current walkthrough step is about
COLOR_EDGE = "#8E8E8E"
COLOR_TEXT = "#222222"
COLOR_WARN = "#9A2A2A"
COLOR_CODE_BG = "#FBFBF8"
COLOR_CODE_HL = "#FFF1B8"

NODE_R = 0.3  # node radius in data units


def parallel_rad(ends_map: dict, e: str) -> float:
    """Curvature for edges sharing the same ends, so parallel edges are drawn apart."""
    group = [x for x in ends_map if ends_map[x] == ends_map[e]]
    k, m = group.index(e), len(group)
    if m <= 2:  # one or two copies: symmetric about the straight segment
        return (k - (m - 1) / 2) * 0.42
    # Three or more copies: fan them OUTWARD only, so they do not cross the other edges
    # inside the triangle. arc3 bends towards rad · (dy, -dx); pick the outward sign.
    a, b = sorted(ends_map[e])
    (x1, y1), (x2, y2) = POS[a], POS[b]
    cx = sum(p[0] for p in POS.values()) / len(POS)
    cy = sum(p[1] for p in POS.values()) / len(POS)
    out = (y2 - y1) * ((x1 + x2) / 2 - cx) - (x2 - x1) * ((y1 + y2) / 2 - cy)
    return (1 if out > 0 else -1) * k * 0.36


def default_edge_color(ends_map: dict, e: str) -> str:
    if is_loop(ends_map, e):
        return COLOR_LOOP
    if sum(ends_map[x] == ends_map[e] for x in ends_map) > 1:
        return COLOR_PARALLEL
    return COLOR_EDGE


def draw_edges(ax, ends_map: dict, edge_colors: dict[str, str] | None = None,
               emphasized: frozenset[str] = frozenset(), labels: bool = True,
               width: float = 3.0, shrink: float = 18) -> None:
    """Draw every edge. `edge_colors` overrides colours; `emphasized` edges are drawn extra
    thick with a dark outline (the edge a walkthrough step is talking about)."""
    edge_colors = edge_colors or {}
    for e, s in ends_map.items():
        color = edge_colors.get(e, default_edge_color(ends_map, e))
        lw, z, effects = width, 2, None
        if e in emphasized:
            lw, z = width * 1.7, 2.5
            effects = [pe.withStroke(linewidth=width * 2.6, foreground="#333333")]
        pts = sorted(s)
        if len(pts) == 1:  # loop: a circle sitting next to the vertex
            (x, y), (dx, dy) = POS[pts[0]], LOOP_DIR[pts[0]]
            patch = Circle((x + 0.5 * dx, y + 0.5 * dy), 0.3, fill=False, edgecolor=color,
                           linewidth=lw, zorder=z, linestyle="--")
            lx, ly = x + 0.95 * dx, y + 0.95 * dy
        else:
            (x1, y1), (x2, y2) = POS[pts[0]], POS[pts[1]]
            rad = parallel_rad(ends_map, e)
            patch = FancyArrowPatch((x1, y1), (x2, y2), arrowstyle="-",
                                    connectionstyle=f"arc3,rad={rad}", color=color,
                                    linewidth=lw, shrinkA=shrink, shrinkB=shrink, zorder=z)
            # midpoint of the quadratic Bézier used by arc3
            lx = (x1 + x2) / 2 + 0.5 * rad * (y2 - y1)
            ly = (y1 + y2) / 2 - 0.5 * rad * (x2 - x1)
        if effects:
            patch.set_path_effects(effects)
        ax.add_patch(patch)
        if labels:
            ax.text(lx, ly, e, fontsize=9, color="#444444", ha="center", va="center",
                    zorder=3, bbox=dict(boxstyle="round,pad=0.15", fc="white", ec="none",
                                        alpha=0.9))


def draw_vertices(ax, ends_map: dict, tags: dict[int, str] | None = None,
                  badges: bool = True, dup: frozenset[int] = frozenset(),
                  r: float = NODE_R, fontsize: float = 15, hidden: bool = False) -> None:
    """Vertices with their names; `badges` adds a 'deg = k' label; `dup` vertices (sharing a
    degree with another vertex) get a red badge; `tags` adds a gold halo + tag. With
    `hidden`, badges read 'deg = ?' so a learner can predict the degree first."""
    tags = tags or {}
    for v in V:
        x, y = POS[v]
        if v in tags:
            ax.add_patch(Circle((x, y), r + 0.17, facecolor=COLOR_FOCUS, alpha=0.55,
                                edgecolor="none", zorder=3.5))
        ax.add_patch(Circle((x, y), r, facecolor=COLOR_VERTEX, edgecolor="#2A4F85",
                            linewidth=1.5, zorder=4))
        ax.text(x, y, str(v), ha="center", va="center", fontsize=fontsize, fontweight="bold",
                color="white", zorder=5)
        if badges:
            dx, dy = BADGE_OFF[v]
            bad = v in dup and not hidden
            label = "deg = ?" if hidden else f"deg = {deg(ends_map, v)}"
            if hidden:  # neutral: the colour must not reveal whether a degree repeats
                fg, fc, ec = "#444444", "#EEEEEE", "#999999"
            elif bad:
                fg, fc, ec = COLOR_WARN, "#FBE3E3", COLOR_WARN
            else:
                fg, fc, ec = "#1B4D2C", "#E3F3E8", COLOR_OK
            ax.text(x + dx, y + dy, label, ha="center", va="center",
                    fontsize=fontsize * 0.72, fontweight="bold", zorder=6, color=fg,
                    bbox=dict(boxstyle="round,pad=0.25", fc=fc, ec=ec))
        if v in tags:
            ax.text(x - r - 0.22, y, tags[v], ha="right", va="center", fontsize=11,
                    fontweight="bold", color="#5A4500", zorder=6,
                    bbox=dict(boxstyle="round,pad=0.2", fc="#FFF4C2", ec=COLOR_FOCUS))


def frame(ax, xlim=(-1.25, 5.25), ylim=(-1.05, 2.55)) -> None:
    ax.set_xlim(*xlim)
    ax.set_ylim(*ylim)
    ax.set_aspect("equal")
    ax.axis("off")


def dup_vertices(ends_map: dict) -> frozenset[int]:
    return frozenset(v for p in equal_degree_pairs(ends_map) for v in p)


def fmt_edges(ends_map: dict) -> str:
    return ", ".join(f"{e} = {{{', '.join(map(str, sorted(s)))}}}" for e, s in ends_map.items())


def deg_formula(ends_map: dict, v: int) -> str:
    inc, lp = incident_edges(ends_map, v), loops_at(ends_map, v)
    s = f"deg({v}) = {len(inc)} incident edge{'s' * (len(inc) != 1)}"
    if inc:
        s += f" ({', '.join(inc)})"
    s += f" + {len(lp)} loop{'s' * (len(lp) != 1)} counted again = {deg(ends_map, v)}"
    return s


# ---------------------------------------------------------------------------
# 5. Static summary figure (visualizations/supp08.png)
# ---------------------------------------------------------------------------

def build_figure(stats: dict) -> plt.Figure:
    fig = plt.figure(figsize=(19, 14), facecolor="white")
    gs = GridSpec(3, 4, figure=fig, height_ratios=[0.8, 1.05, 0.62], hspace=0.3, wspace=0.1,
                  left=0.03, right=0.97, top=0.86, bottom=0.03)

    fig.suptitle("Supplementary Exercise 8:  the claim is FALSE  (a counterexample)",
                 fontsize=19, fontweight="bold", color=COLOR_TEXT, y=0.985)
    fig.text(0.5, 0.955,
             "Claim: \"There are always two vertices of the same degree in a finite multigraph "
             "having at least two vertices.\"   The Lean theorem GraphCh10.supp08 proves "
             "¬ (this claim) using the graph ex8 below.",
             ha="center", fontsize=10.5, color="#444444")
    fig.text(0.5, 0.937,
             "Here one example IS the whole proof: a single multigraph that breaks a "
             "\"for every\" statement disproves it.  "
             "Run  py visualizations/supp08.py  (any Python with matplotlib + networkx) "
             "for the interactive walkthrough.",
             ha="center", fontsize=10.5, color=COLOR_WARN, style="italic")

    # Row 0: the counterexample, then how each degree is counted.
    ax = fig.add_subplot(gs[0, 0])
    draw_edges(ax, EX8_ENDS)
    draw_vertices(ax, EX8_ENDS)
    frame(ax)
    ax.set_title("The multigraph ex8", fontsize=13, fontweight="bold", pad=22)
    ax.text(0.5, 1.015, fmt_edges(EX8_ENDS) + ";  e1, e2 are parallel",
            transform=ax.transAxes, ha="center", va="bottom", fontsize=9.3, color="#444444")

    for v in V:
        ax = fig.add_subplot(gs[0, 1 + v])
        inc = incident_edges(EX8_ENDS, v)
        draw_edges(ax, EX8_ENDS, {e: COLOR_FOCUS for e in inc}, frozenset(inc))
        draw_vertices(ax, EX8_ENDS, tags={v: "v"})
        frame(ax)
        ax.set_title(f"deg({v}) = {EX8_DEG[v]}", fontsize=13, fontweight="bold", pad=22)
        ax.text(0.5, 1.015, deg_formula(EX8_ENDS, v).split(" = ", 1)[1],
                transform=ax.transAxes, ha="center", va="bottom", fontsize=9.3,
                color="#444444")

    # Row 1 left: the 9 cases of `match u, w with`.
    ax = fig.add_subplot(gs[1, :2])
    ax.axis("off")
    rows = []
    for u, w in PAIRS:
        if u == w:
            rows.append([f"| {u}, {w}", "—", "—", "u = w", "absurd rfl hne"])
        else:
            rows.append([f"| {u}, {w}", str(EX8_DEG[u]), str(EX8_DEG[w]),
                         f"{EX8_DEG[u]} ≠ {EX8_DEG[w]}",
                         f"rw [h{u}, h{w}]; decide"])
    table = ax.table(cellText=rows,
                     colLabels=["case u, w", "deg u", "deg w", "result", "Lean closes it with"],
                     loc="center", cellLoc="center", colWidths=[0.14, 0.11, 0.11, 0.2, 0.34])
    table.auto_set_font_size(False)
    table.set_fontsize(10.5)
    table.scale(1, 1.75)
    for (r, c), cell in table.get_celld().items():
        cell.set_edgecolor("#CCCCCC")
        if r == 0:
            cell.set_facecolor("#EFEFEF")
            cell.set_text_props(fontweight="bold")
        elif c == 3:
            diag = PAIRS[r - 1][0] == PAIRS[r - 1][1]
            cell.set_text_props(color="#777777" if diag else COLOR_OK, fontweight="bold")
        elif c in (0, 4):
            cell.set_text_props(family="DejaVu Sans Mono")
    ax.set_title("hDistinct: all 9 cases of  match u, w with  (computed)", fontsize=13,
                 fontweight="bold", pad=22)
    ax.text(0.5, 1.015, "every pair with u ≠ w has different degrees, so no pair can satisfy "
            "u ≠ w ∧ deg u = deg w", transform=ax.transAxes, ha="center", va="bottom",
            fontsize=9.5, color="#444444")

    # Row 1 right: all 8 simple graphs on 3 vertices -- each repeats a degree.
    sub = GridSpecFromSubplotSpec(2, 4, subplot_spec=gs[1, 2:], wspace=0.05, hspace=0.25)
    simple = list(multigraphs_on(V, 1))
    for i, g in enumerate(simple):
        ax = fig.add_subplot(sub[i // 4, i % 4])
        m = as_map(g)
        draw_edges(ax, m, labels=False, width=2.2, shrink=11)
        draw_vertices(ax, m, dup=dup_vertices(m), r=0.36, fontsize=11)
        frame(ax, (-1.0, 5.0), (-1.2, 2.6))
        pairs = equal_degree_pairs(m)
        ax.set_title(f"vertices {pairs[0][0]} and {pairs[0][1]}: same degree", fontsize=9.5,
                     color=COLOR_WARN, pad=2)
    ax0 = fig.add_subplot(gs[1, 2:], frameon=False)
    ax0.set_xticks([])
    ax0.set_yticks([])
    ax0.set_title("Why the parallel edge matters: all 8 SIMPLE graphs on 3 vertices",
                  fontsize=13, fontweight="bold", pad=40)
    ax0.text(0.5, 1.015, "Pigeonhole: n vertices, possible degrees 0..n−1, but 0 and n−1 cannot "
             "both occur, so only n−1 values remain for n vertices.\n"
             f"Checked by this script for all {stats['n_simple']:,} labelled simple graphs on 2 to 5 "
             "vertices (the general argument is not formalized in this project).",
             transform=ax0.transAxes, ha="center", va="bottom", fontsize=9.5, color="#444444")

    # Row 2: proof correspondence.
    ax = fig.add_subplot(gs[2, :])
    ax.axis("off")
    ax.add_patch(plt.Rectangle((0, 0), 1, 1, transform=ax.transAxes, facecolor="#F7F7F7",
                               edgecolor="#D0D0D0", linewidth=1))
    left = ["The Lean proof, step by step  (theorem supp08 : ¬ ∀ V E G, ... )",
            "intro claim            assume the claim, for contradiction (goal: False)",
            "have hMulti            ex8 has no loops: e0, e1, e2 each join two different vertices",
            "have hCard             Fintype.card (Fin 3) = 3, and 2 ≤ 3",
            "have hDeg              deg 0 = {0}, deg 1 = {1}, deg 2 = {2}  (counted by decide)".format(
                EX8_DEG[0], EX8_DEG[1], EX8_DEG[2]),
            "have hDistinct         u ≠ w → deg u ≠ deg w   (the 9 cases in the table)",
            "obtain ⟨u, w, hne, hEq⟩ := claim (Fin 3) (Fin 3) ex8 hMulti hCard",
            "exact hDistinct u w hne hEq      deg u ≠ deg w  contradicts  deg u = deg w  ∎"]
    right = ["Checked by assertions in this script",
             "• ex8 is read from GraphCh10/DefinitionTests.lean; degrees from the `deg` definition",
             "• the degrees match the Lean line  have hDeg : ...  and NetworkX's degree",
             "• ex8 has no loops, 3 ≥ 2 vertices, and pairwise different degrees",
             "• on 2 vertices every multigraph has equal degrees, and every 3-vertex",
             f"  counterexample has ≥ 3 edges ({stats['n_three']} edge multisets with exactly 3)",
             "• every labelled simple graph on 2..5 vertices repeats a degree (pigeonhole)"]
    for x, lines, w in ((0.015, left, 0.56), (0.6, right, 0.39)):
        ax.text(x, 0.92, lines[0], transform=ax.transAxes, fontsize=11.5, fontweight="bold",
                va="top", color=COLOR_TEXT)
        ax.text(x, 0.78, "\n".join(lines[1:]), transform=ax.transAxes, fontsize=10,
                va="top", color=COLOR_TEXT, family="DejaVu Sans Mono" if x < 0.5 else None,
                linespacing=1.55)

    legend = [
        Patch(facecolor=COLOR_VERTEX, edgecolor="#2A4F85", label="vertex"),
        Line2D([], [], color=COLOR_EDGE, linewidth=3, label="edge"),
        Line2D([], [], color=COLOR_PARALLEL, linewidth=3, label="parallel edges (same ends)"),
        Line2D([], [], color=COLOR_FOCUS, linewidth=4, label="edges counted in deg(v)"),
        Patch(facecolor="#E3F3E8", edgecolor=COLOR_OK, label="degree not shared"),
        Patch(facecolor="#FBE3E3", edgecolor=COLOR_WARN, label="degree shared with another vertex"),
    ]
    fig.legend(handles=legend, loc="upper center", ncol=6, frameon=False, fontsize=10,
               bbox_to_anchor=(0.5, 0.927))
    return fig


# ---------------------------------------------------------------------------
# 6. Lean source, read from the project (the source of truth)
# ---------------------------------------------------------------------------

def read_lean_sources() -> dict[str, list[str]]:
    """The proof of `supp08` and the definitions it uses, read verbatim from disk."""
    proof_lines = _require(PROOF_FILE)
    start = next(i for i, ln in enumerate(proof_lines) if ln.startswith("theorem supp08"))
    end = next(i for i, ln in enumerate(proof_lines)
               if i > start and "exact hDistinct u w hne hEq" in ln)
    proof = proof_lines[start:end + 1]

    def_lines = _require(DEFS_FILE)

    def find(prefix: str, extra: int = 0) -> list[str]:
        hits = [i for i, ln in enumerate(def_lines) if ln.strip().startswith(prefix)]
        assert len(hits) == 1, f"expected exactly one line starting with {prefix!r}"
        return [ln.rstrip() for ln in def_lines[hits[0]:hits[0] + extra + 1]]

    defs = [
        "-- GraphCh10/Definitions.lean (excerpt; docstrings omitted)",
        *find("structure UGraph"),
        *find("ends : E → Sym2 V"),
        "",
        "namespace UGraph   -- inside: variable (G : UGraph V E)",
        "",
        *find("def IsLoop (e : E) : Prop := (G.ends e).IsDiag"),  # UGraph's, not DGraph's
        *find("def IsMultigraph"),
        "",
        *find("def Incident"),
        "",
        *find("def deg", extra=2),
        "",
        "-- GraphCh10/DefinitionTests.lean (the counterexample)",
        EX8_SOURCE,
    ]
    return {"proof": proof, "defs": defs}


# ---------------------------------------------------------------------------
# 7. The walkthrough: graph basics, then the Lean proof line by line
# ---------------------------------------------------------------------------
# Each step: part, title, which code to show ("defs" or "proof"), substrings that pick
# the highlighted code lines (`dyn_anchor(focus)` adds one more for the current example),
# a focus kind (what to highlight on the graph), and two explanations. `math` may be a
# function of (explorer, focus).

EDITED = ("⚠ You have edited the graph, so it is no longer ex8. The Lean proof is about "
          "ex8 only. Press 'Reset to ex8' to compare with the proof. ")


def _deg_list(ex) -> str:
    d = ex.degs
    return ", ".join(f"deg({v}) = {'?' if ex.hidden else d[v]}" for v in V)


# Lean goal states shown in the "Lean's goal" box. They were captured from Lean's infoview
# (the lean_goal tool on GraphCh10/Exercises/Supp08.lean) and abbreviated: the long
# hypothesis `claim` is written `claim : ∀ (V E : Type) …` and earlier facts are summarized.
# They always describe ex8 (the Lean proof is only about ex8), so they use EX8_DEG.
GOAL_INTRO_BEFORE = ("⊢ ¬∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq V] (G : UGraph V E),\n"
                     "      G.IsMultigraph → 2 ≤ Fintype.card V → ∃ u w, u ≠ w ∧ G.deg u = G.deg w")


def _goal_pair(f) -> list[str]:
    u, w = f["u"], f["w"]
    lines = ["after intro u w hne:   u w : Fin 3    hne : u ≠ w    ⊢ ex8.deg u ≠ ex8.deg w",
             "after obtain:          h0 : ex8.deg 0 = {0}   h1 : ex8.deg 1 = {1}   "
             "h2 : ex8.deg 2 = {2}".format(EX8_DEG[0], EX8_DEG[1], EX8_DEG[2]),
             f"in case | {u}, {w}:        hne : {u} ≠ {w}    ⊢ ex8.deg {u} ≠ ex8.deg {w}"]
    if u == w:
        lines.append(f"exact absurd rfl hne:  rfl : {u} = {u} and hne : ¬({u} = {u}) contradict"
                     "  →  no goals")
    else:
        lines += [f"after rw [h{u}, h{w}]:     ⊢ {EX8_DEG[u]} ≠ {EX8_DEG[w]}",
                  "after decide:          no goals"]
    return lines


STEPS: list[dict] = [
    dict(
        part="Part 1 · Graph basics", title="Vertices and edges", code="defs",
        anchors=["structure UGraph", "ends : E → Sym2 V", "def ex8"], focus=None,
        math=lambda ex, f: (
            "A graph has vertices (the blue circles 0, 1, 2) and edges (the lines e0, e1, "
            "e2). Each edge has a set of endpoints: e0 joins 0 and 1, while e1 and e2 both "
            "join 1 and 2. This graph is called ex8; it is read from the Lean file. "
            "The degrees are hidden ('deg = ?') until you work them out in step 3."),
        lean=("`structure UGraph (V E)` has one field, `ends`, giving each edge its endpoints. "
              "`Sym2 V` means 'an unordered pair of vertices', written s(u, w), so "
              "s(0, 1) = s(1, 0). `Fin 3` is the type {0, 1, 2}: ex8 has vertices 0, 1, 2 and "
              "edges 0, 1, 2 (drawn as e0, e1, e2). `if e = 0 then s(0, 1) else s(1, 2)`: "
              "edge 0 joins 0 and 1, every other edge joins 1 and 2."),
    ),
    dict(
        part="Part 1 · Graph basics", title="Parallel edges and loops: what a multigraph is",
        code="defs", anchors=["def IsLoop (e : E)", "def IsMultigraph"], focus="parallel",
        math=lambda ex, f: (
            "Parallel (or multiple) edges are different edges with the same endpoints: here "
            "e1 and e2 (gold now, orange in other steps). A loop joins a vertex to itself. "
            "A multigraph may have parallel edges but no loops. A simple graph has neither. "
            "So ex8 is a multigraph but not a simple graph."),
        lean=("`IsLoop e := (G.ends e).IsDiag`: `IsDiag` means both ends are the same vertex, "
              "as in s(v, v). `IsMultigraph := ∀ e : E, ¬ G.IsLoop e` reads 'for every edge e, "
              "e is not a loop' (`¬` = not). Nothing forbids two edges with equal `ends`, so "
              "parallel edges are allowed."),
    ),
    dict(
        part="Part 1 · Graph basics", title="The degree of a vertex",
        code="defs", anchors=["def Incident", ("def deg", 3)], focus="degree",
        math=lambda ex, f: (
            "The degree of v is the number of edges touching v, with loops counted twice. "
            "Each parallel edge is a separate edge, so each one counts. "
            + ("Predict first: count the edges at each vertex yourself, then press "
               "'Show degrees' to check. " if ex.hidden else
               "To practise again, press 'Hide degrees'. ") +
            f"Gold: the edges counted for v = {f['v']}. "
            f"{ex.formula(f['v'])}. Click a vertex or press 'Next example'."),
        lean=("`deg v` adds two counts. `Finset.univ.filter (fun e => G.Incident e v)` is "
              "'the set of all edges e with v as an endpoint' (`Finset.univ` = all edges, "
              "`filter` keeps those passing the test), and `.card` is its size. The second "
              "count adds each loop at v once more. `[Fintype E]` says there are finitely "
              "many edges, so these counts make sense."),
    ),
    dict(
        part="Part 1 · Graph basics", title="Try it: edit the graph",
        code="defs", anchors=[("def deg", 3)], focus=None,
        math=lambda ex, f: (
            "Use − / + to remove or add copies of an edge and watch the degrees and the "
            "panel below the graph update. Remove one copy of {1, 2}: the degrees become "
            "1, 2, 1 and a degree repeats. Add a loop: the graph is no longer a multigraph. "
            f"Can you find another counterexample? Right now: {_deg_list(ex)}."),
        lean=("This step uses no Lean. The panel recomputes `IsMultigraph` and `deg` from "
              "the edges, following the definitions on the right. 'Reset to ex8' restores "
              "the graph used by the proof."),
    ),
    dict(
        part="Part 1 · Graph basics", title="The claim, and how to disprove it",
        code="proof", anchors=["¬ ∀ (V E : Type)", "(G : UGraph V E),",
                               "G.IsMultigraph → 2 ≤ Fintype.card V →",
                               "∃ u w : V, u ≠ w ∧ G.deg u = G.deg w"], focus=None,
        goal=lambda ex, f: ["the goal at the start of the proof:", GOAL_INTRO_BEFORE],
        math=lambda ex, f: (
            "The claim: EVERY finite multigraph with at least two vertices has two different "
            "vertices of the same degree. A 'for every' statement is false as soon as ONE "
            "example breaks it; that example is a counterexample. ex8 is one: a finite "
            "multigraph with 3 ≥ 2 vertices whose degrees 1, 3, 2 are all different."),
        lean=("The theorem states the NEGATION `¬ ∀ …` of the claim. `∀ (V E : Type)` ranges "
              "over all vertex and edge types. The square-bracket arguments are filled in "
              "by Lean automatically: `[Fintype V]` = V is finite, `[DecidableEq V]` = Lean "
              "can test u = w, which it needs to count. The arrows `→` list the hypotheses, "
              "and `∃ u w : V, u ≠ w ∧ …` reads 'there are u, w with u ≠ w and …'."),
    ),
    dict(
        part="Part 2 · The Lean proof", title="intro claim: assume the claim",
        code="proof", anchors=["intro claim", "assume, for contradiction"], focus=None,
        goal=lambda ex, f: ["before:  " + GOAL_INTRO_BEFORE.replace("\n", "\n         "),
                            "after:   claim : ∀ (V E : Type) … → ∃ u w, u ≠ w ∧ G.deg u = G.deg w",
                            "         ⊢ False"],
        math=lambda ex, f: (
            "To prove 'not P': assume P and derive something impossible. "
            "So suppose every finite multigraph with at least two vertices has two vertices "
            "of equal degree. We will apply this to ex8 and see it fail."),
        lean=("In Lean, `¬ P` is by definition `P → False` ('P leads to something impossible'), "
              "so no special contradiction rule is needed. "
              "`intro claim` assumes P and calls it `claim`; the goal becomes `False`. In the "
              "goal box, `⊢` marks what is still to prove and the lines above it are what we "
              "may use."),
    ),
    dict(
        part="Part 2 · The Lean proof", title="have hMulti: ex8 is a multigraph",
        code="proof", anchors=["has no loops, so it is a multigraph", ("have hMulti", 3)],
        focus="edge",
        goal=lambda ex, f: ["before:        ⊢ ex8.IsMultigraph",
                            "after unfold:  ⊢ ∀ (e : Fin 3), ¬(ex8.ends e).IsDiag",
                            "after decide:  no goals   (hMulti : ex8.IsMultigraph is now known)"],
        math=lambda ex, f: (
            "Every edge must join two DIFFERENT vertices. The graph has no edges right now, "
            "so there is no loop and it is a multigraph."
        ) if f["e"] is None else (
            "Every edge must join two DIFFERENT vertices. "
            f"Gold: {f['e']} = {{{', '.join(map(str, sorted(ex.ends[f['e']])))}}}, "
            f"{'a loop!' if is_loop(ex.ends, f['e']) else 'two different vertices, not a loop'}. "
            f"Whole graph a multigraph? {'yes' if is_multigraph(ex.ends) else 'NO'}. "
            "'Next example' shows the other edges."),
        lean=("`have hMulti : ex8.IsMultigraph := by …` proves a fact and names it `hMulti`. "
              "`unfold` replaces the names `IsMultigraph`, `IsLoop` by their definitions (see "
              "the goal box). Why first? `decide` only works on statements Lean knows how to "
              "check by computation; `IsMultigraph` is just a name, and after `unfold` the goal "
              "is 'for every e in Fin 3, …', which `decide` checks for the 3 edges one by one. "
              "Lean's kernel (its small, trusted checker) re-checks the computation."),
    ),
    dict(
        part="Part 2 · The Lean proof", title="have hCard: at least two vertices",
        code="proof", anchors=["it has three vertices, so at least two", ("have hCard", 3)],
        focus="card",
        goal=lambda ex, f: ["before:                  ⊢ 2 ≤ Fintype.card (Fin 3)",
                            "after rw [card_fin]:     ⊢ 2 ≤ 3",
                            "after decide:            no goals   (hCard is now known)"],
        math=lambda ex, f: (
            "Count the vertices: 0, 1, 2. There are 3, and 2 ≤ 3, so ex8 meets the second "
            "hypothesis of the claim."),
        lean=("`Fintype.card (Fin 3)` is the number of elements of `Fin 3`. `rw [Fintype."
              "card_fin]` rewrites with the library fact `Fintype.card (Fin n) = n`, so the "
              "goal becomes `2 ≤ 3`. `decide` checks `2 ≤ 3` by computation."),
    ),
    dict(
        part="Part 2 · The Lean proof", title="have hDeg: the three degrees",
        code="proof", anchors=["its degrees are deg(0) = 1", ("have hDeg", 2)], focus="degree",
        goal=lambda ex, f: ["before:        ⊢ " + " ∧ ".join(f"ex8.deg {v} = {EX8_DEG[v]}"
                                                          for v in V),
                            "after decide:  no goals   (hDeg is now known)"],
        math=lambda ex, f: (
            f"Count the edges at each vertex. {ex.formula(f['v'])}. In ex8: deg(0) = 1, "
            "deg(1) = 3 (e0 and both parallel edges), deg(2) = 2. 'Next example' or a click "
            "shows the other vertices."),
        lean=("`A ∧ B` means 'A and B', so the statement is three equations at once. Each "
              "`deg` is the size of a filtered finite set of edges, so `decide` simply counts: "
              "it evaluates `ex8.deg 0` to 1, and so on, and the kernel re-checks the counting."),
    ),
    dict(
        part="Part 2 · The Lean proof", title="have hDistinct: different vertices, different degrees",
        code="proof", anchors=["have hDistinct", "intro u w hne", "obtain ⟨h0, h1, h2⟩ := hDeg",
                               "match u, w with"],
        dyn_anchor=lambda f: f"| {f['u']}, {f['w']} =>", focus="pair",
        goal=lambda ex, f: _goal_pair(f),
        math=lambda ex, f: (
            "Check every pair (u, w) of vertices. "
            + (f"Here u = w = {f['u']}: this case cannot happen, because we assumed u ≠ w."
               if f['u'] == f['w'] else
               f"Here u = {f['u']}, w = {f['w']}: deg u = {ex.degs[f['u']]}, "
               f"deg w = {ex.degs[f['w']]}, "
               + ("different ✓." if ex.degs[f['u']] != ex.degs[f['w']]
                  else "EQUAL, so this edited graph is not a counterexample.")) +
            f" (Case {f['k'] + 1} of 9; 'Next example' shows the next one.)"),
        lean=("`intro u w hne` takes any u, w and the assumption `hne : u ≠ w`. `obtain ⟨h0, "
              "h1, h2⟩ := hDeg` splits the 'and' into three equations (⟨ ⟩ are ANGLE "
              "brackets, not parentheses; they take apart ∧ and ∃). `match u, w with` tries all 9 value "
              "pairs and substitutes them everywhere, so `hne` becomes e.g. `0 ≠ 0`. "
              "`absurd h hn` proves anything from `h : A` and `hn : ¬A`; with `rfl : 0 = 0` it "
              "closes the impossible cases. Otherwise `rw` replaces degrees by numbers and "
              "`decide` checks e.g. `1 ≠ 3`."),
    ),
    dict(
        part="Part 2 · The Lean proof", title="obtain … := claim … ex8: use the claim on ex8",
        code="proof", anchors=["obtain ⟨u, w, hne, hEq⟩ := claim", "applied to `ex8`"],
        focus="claim",
        goal=lambda ex, f: ["before:  (claim, hMulti, hCard, hDeg, and hDistinct : ∀ (u w : Fin 3), "
                            "u ≠ w → ex8.deg u ≠ ex8.deg w)   ⊢ False",
                            "after:   (all of those, plus)  u w : Fin 3   hne : u ≠ w   "
                            "hEq : ex8.deg u = ex8.deg w",
                            "         ⊢ False"],
        math=lambda ex, f: (
            "The assumed claim is about EVERY multigraph, so it applies to ex8, whose "
            "hypotheses we checked (hMulti, hCard). It promises two vertices u ≠ w with "
            "deg u = deg w; the question marks show the promise. But ex8 has no such pair."),
        lean=("`claim (Fin 3) (Fin 3) ex8 hMulti hCard` plugs ex8 into the ∀, like calling a "
              "function. The square-bracket arguments are found automatically, and `hMulti`, "
              "`hCard` are passed as the two hypotheses. The result is `∃ u w, u ≠ w ∧ "
              "ex8.deg u = ex8.deg w`; `obtain ⟨u, w, hne, hEq⟩` (angle brackets) names its "
              "four parts: the two vertices and the two facts."),
    ),
    dict(
        part="Part 2 · The Lean proof", title="exact hDistinct u w hne hEq: contradiction ∎",
        code="proof", anchors=["-- contradiction", "exact hDistinct u w hne hEq"], focus=None,
        goal=lambda ex, f: ["before:  hne : u ≠ w    hEq : ex8.deg u = ex8.deg w    "
                            "hDistinct : … → ex8.deg u ≠ ex8.deg w    ⊢ False",
                            "after:   no goals: the proof is complete ∎"],
        math=lambda ex, f: (
            "hDistinct says the two degrees are different; the claim said they are equal. "
            "Both cannot be true, so the assumption was false and the claim is disproved."),
        lean=("`hDistinct u w hne` has type `ex8.deg u ≠ ex8.deg w`, and `a ≠ b` means "
              "`a = b → False`. Applying it to `hEq : ex8.deg u = ex8.deg w` gives `False`, "
              "exactly the goal. `exact` closes it and the kernel re-checks the whole proof."),
    ),
    dict(
        part="Part 3 · Why this works", title="Checking one example vs. proving 'for every'",
        code="proof", anchors=[], focus=None,
        math=lambda ex, f: (
            "To PROVE a 'for every' statement, checking examples is never enough: there are "
            "infinitely many graphs, so you need an argument that covers all of them at once. "
            "To DISPROVE one, a single counterexample is enough. That is why this proof only "
            "looks at ex8, and why it is still a complete answer."),
        lean=("The Lean proof never inspects any graph except ex8: every fact it checks is "
              "about ex8 or about small numbers like 2 ≤ 3. At the last build, `#print axioms "
              "GraphCh10.supp08` (GraphCh10/Verification/Verify08.lean) reported only Lean's "
              "standard axioms propext, Classical.choice and Quot.sound: no `sorry`, no project "
              "axioms, no `native_decide`. Re-run that file to re-check."),
    ),
    dict(
        part="Part 3 · Why this works", title="Why the parallel edge is essential (pigeonhole)",
        code="proof", anchors=[], focus="simple",
        math=lambda ex, f: (
            "In a SIMPLE graph with n vertices each degree is between 0 and n − 1 (n "
            "possible values). Degrees 0 and n − 1 cannot both occur: a vertex of degree "
            "n − 1 touches every other vertex, so none has degree 0. Then n vertices share "
            "at most n − 1 values, so two must be equal (pigeonhole). A parallel edge lets "
            "deg(1) reach 3 = n, escaping this. 'Next example' shows all 8 simple graphs on "
            "3 vertices, each with a repeated degree (red). Also, ex8 is as small as possible: "
            "with 2 vertices both degrees are always equal, and every 3-vertex counterexample "
            "has at least 3 edges."),
        lean=lambda ex: (
            "This step is NOT formalized in the project; it explains why the counterexample "
            f"needs a parallel edge. The script checks it on all {ex.stats['n_simple']:,} "
            "labelled simple graphs with 2 to 5 vertices. Minimality is checked on every "
            "multigraph with at most 3 copies of each pair (enough, since 2 edges use at most "
            "2 copies) and, on 2 vertices, up to 4 copies (there deg 0 = deg 1 always)."),
    ),
]

PAIR_KEYS = [("01", 0, 1), ("02", 0, 2), ("12", 1, 2)]


def highlighted_lines(src: list[str], anchors) -> set[int]:
    """Indices of the source lines to highlight. An anchor is a substring that must occur on
    exactly one line, or a pair (substring, n) meaning that line and the n − 1 lines after it
    (used to highlight a whole `have … := by` block, including its `decide` line)."""
    idx: set[int] = set()
    for a in anchors:
        sub, n = (a, 1) if isinstance(a, str) else a
        hits = [i for i, ln in enumerate(src) if sub in ln]
        assert len(hits) == 1, f"anchor {sub!r} matches {len(hits)} lines"
        idx.update(range(hits[0], min(len(src), hits[0] + n)))
    return idx


# ---------------------------------------------------------------------------
# 8. The interactive explorer
# ---------------------------------------------------------------------------

class Explorer:
    """Interactive companion: inspect degrees, edit the graph, step through the proof."""

    def __init__(self, stats: dict):
        self.stats = stats
        self.lean = read_lean_sources()
        self._check_anchors()
        self.ends: dict[str, frozenset[int]] = dict(EX8_ENDS)
        self.step = 0
        self.example_idx = 0
        self.hidden = True  # degrees start hidden: predict first (steps 1-3), then check
        self.revealed = False  # set once degrees have been shown
        self.selected: int | None = None  # last clicked vertex

        for key in ("keymap.back", "keymap.forward"):  # free ← / → for the walkthrough
            plt.rcParams[key] = [k for k in plt.rcParams[key] if k not in ("left", "right")]

        self.fig = plt.figure(figsize=(18, 11.5), facecolor="white")
        try:
            self.fig.canvas.manager.set_window_title("Supp. 8: a counterexample")
        except AttributeError:
            pass
        self.fig.text(0.015, 0.972,
                      "Supplementary Exercise 8:  two vertices of the same degree?  No!",
                      fontsize=18, fontweight="bold", color=COLOR_TEXT, va="center")
        self.fig.text(0.015, 0.94,
                      "An interactive companion to the Lean proof GraphCh10.supp08. A single "
                      "multigraph, ex8, breaks the claim, and that one example disproves it.",
                      fontsize=10.5, color=COLOR_WARN, style="italic", va="center")

        self.ax_graph = self.fig.add_axes([0.015, 0.36, 0.465, 0.475])
        self.caption = self.fig.text(0.2475, 0.872, "", ha="center", va="top", fontsize=10.5,
                                     color=COLOR_TEXT, linespacing=1.5)
        self.ax_legend = self.fig.add_axes([0.015, 0.29, 0.465, 0.07])
        self.ax_edit = self.fig.add_axes([0.015, 0.03, 0.165, 0.245])
        self.ax_sets = self.fig.add_axes([0.19, 0.03, 0.29, 0.245])
        self.ax_text = self.fig.add_axes([0.505, 0.64, 0.48, 0.28])
        self.ax_goal = self.fig.add_axes([0.505, 0.505, 0.48, 0.125])
        self.ax_code = self.fig.add_axes([0.505, 0.105, 0.48, 0.39])
        for ax in (self.ax_legend, self.ax_edit, self.ax_sets, self.ax_text, self.ax_goal,
                   self.ax_code):
            ax.axis("off")
        self.fig.text(0.015, 0.905,
                      "Click a vertex to see how its degree is counted.   "
                      "Gold marks what the current step is about.",
                      fontsize=9.8, color="#444444", va="center")

        def button(rect, label, cb, color="#F0F0F0", size=10.5):
            b = Button(self.fig.add_axes(rect), label, color=color, hovercolor="#DDE8F5")
            b.label.set_fontsize(size)
            b.on_clicked(cb)
            return b

        # Graph editor: − / + for each pair, a loop toggle, and reset.
        self.ax_edit.text(0.0, 1.0, "Edit the graph", transform=self.ax_edit.transAxes,
                          fontsize=10.5, fontweight="bold", va="top")
        self.edit_buttons: dict[str, Button] = {}
        for i, (key, a, b) in enumerate(PAIR_KEYS):
            y = 0.225 - i * 0.042
            self.fig.text(0.017, y + 0.0175, f"edge {{{a}, {b}}}", fontsize=10, va="center")
            self.edit_buttons["-" + key] = button(
                [0.085, y, 0.04, 0.035], "−", lambda _e, a=a, b=b: self.remove_edge(a, b))
            self.edit_buttons["+" + key] = button(
                [0.13, y, 0.04, 0.035], "+", lambda _e, a=a, b=b: self.add_edge(a, b))
        self.loop_buttons = {
            v: button([0.017 + 0.052 * v, 0.085, 0.049, 0.035], f"loop at {v}",
                      lambda _e, v=v: self.toggle_loop(v), size=9)
            for v in V}
        self.btn_loop = self.loop_buttons[0]
        self.btn_reset = button([0.017, 0.04, 0.153, 0.035], "Reset to ex8",
                                lambda _e: self.reset(), color="#E3EEDF", size=9.5)

        self.btn_prev = button([0.505, 0.035, 0.085, 0.055], "◀ Previous", lambda _e: self.go(-1))
        self.btn_next = button([0.700, 0.035, 0.085, 0.055], "Next ▶", lambda _e: self.go(+1),
                               color="#E3EEDF")
        self.btn_example = button([0.795, 0.035, 0.09, 0.055], "Next example",
                                  lambda _e: self.next_example())
        self.btn_hide = button([0.895, 0.035, 0.09, 0.055], "Show degrees",
                               lambda _e: self.toggle_hidden(), color="#FFF4C2")
        self.step_label = self.fig.text(0.6425, 0.0625, "", ha="center", va="center",
                                        fontsize=11, fontweight="bold", color=COLOR_TEXT)

        self._draw_legend()
        self.fig.canvas.mpl_connect("button_press_event", self._on_click)
        self.fig.canvas.mpl_connect("key_press_event", self._on_key)
        self.enter_step(0)

    # -- state --------------------------------------------------------------

    def _check_anchors(self) -> None:
        """Every walkthrough anchor must match exactly one line of the real Lean source."""
        for s in STEPS:
            lines = self.lean[s["code"]]
            anchors = list(s["anchors"])
            if "dyn_anchor" in s:
                anchors += [s["dyn_anchor"](dict(u=u, w=w)) for u, w in PAIRS]
            highlighted_lines(lines, anchors)  # asserts each anchor is unique

    @property
    def degs(self) -> dict[int, int]:
        return degrees(self.ends)

    @property
    def edited(self) -> bool:
        return sorted(self.ends.values(), key=sorted) != sorted(EX8_ENDS.values(), key=sorted)

    def _set_edges(self, ends_list: list[frozenset[int]]) -> None:
        self.ends = as_map(ends_list)  # keep the order, so existing edges keep their names
        self.redraw()

    def add_edge(self, a: int, b: int) -> None:
        if sum(s == sym2(a, b) for s in self.ends.values()) < 3:  # at most 3 parallel copies
            self._set_edges([*self.ends.values(), sym2(a, b)])

    def remove_edge(self, a: int, b: int) -> None:
        lst = list(self.ends.values())
        if sym2(a, b) in lst:
            del lst[len(lst) - 1 - lst[::-1].index(sym2(a, b))]  # remove the LAST copy
            self._set_edges(lst)

    def toggle_loop(self, v: int) -> None:
        lst = list(self.ends.values())
        if sym2(v, v) in lst:
            lst.remove(sym2(v, v))
        else:
            lst.append(sym2(v, v))
        self._set_edges(lst)

    def reset(self) -> None:
        self.ends = dict(EX8_ENDS)
        self.redraw()

    def toggle_hidden(self) -> None:
        """Predict-then-check: hide every computed degree until the learner shows them."""
        self.hidden = not self.hidden
        self.revealed = self.revealed or not self.hidden
        self.btn_hide.label.set_text("Show degrees" if self.hidden else "Hide degrees")
        self.redraw()

    def formula(self, v: int) -> str:
        """How deg(v) is counted, or a prompt to predict it while degrees are hidden."""
        if self.hidden:
            return f"deg({v}) = ?   (count the gold edges yourself; a loop would count twice)"
        return deg_formula(self.ends, v)

    def go(self, delta: int) -> None:
        self.enter_step(max(0, min(len(STEPS) - 1, self.step + delta)))

    def next_example(self) -> None:
        self.example_idx += 1
        self.redraw()

    def enter_step(self, k: int) -> None:
        self.step, self.example_idx = k, 0
        if k >= 3 and not self.revealed:  # from step 4 on the proof needs the numbers
            self.hidden, self.revealed = False, True
            self.btn_hide.label.set_text("Hide degrees")
        self.redraw()

    # -- events -------------------------------------------------------------

    def _on_click(self, event) -> None:
        if event.inaxes is not self.ax_graph or event.button != 1 or event.xdata is None:
            return
        v = min(V, key=lambda w: (POS[w][0] - event.xdata) ** 2 + (POS[w][1] - event.ydata) ** 2)
        if (POS[v][0] - event.xdata) ** 2 + (POS[v][1] - event.ydata) ** 2 <= (1.4 * NODE_R) ** 2:
            self.select_vertex(v)

    def select_vertex(self, v: int) -> None:
        """Clicking a vertex shows its degree; on a 'degree' step it becomes the example."""
        self.selected = v
        if STEPS[self.step]["focus"] == "degree":
            self.example_idx = (V.index(v) - 1) % len(V)
        self.redraw()

    def _on_key(self, event) -> None:
        if event.key == "right":
            self.go(+1)
        elif event.key == "left":
            self.go(-1)

    # -- what to highlight --------------------------------------------------

    def focus_info(self, kind: str | None) -> tuple[dict | None, int]:
        """What the current step highlights in gold / bold. Returns (info, #examples)."""
        sel = self.selected
        if kind is None:
            if sel is None:
                return None, 0
            inc = incident_edges(self.ends, sel)
            return dict(tags={sel: "v"}, edges={e: COLOR_FOCUS for e in inc},
                        caption=self.formula(sel)), 0
        if kind == "parallel":
            par = [e for e in self.ends if default_edge_color(self.ends, e) == COLOR_PARALLEL]
            return dict(tags={}, edges={e: COLOR_FOCUS for e in par},
                        caption=("gold: parallel edges " + ", ".join(par)) if par
                        else "no parallel edges right now"), 1
        if kind == "degree":  # start at vertex 1, where the parallel edges meet
            v = V[(self.example_idx + 1) % len(V)]
            inc = incident_edges(self.ends, v)
            return dict(v=v, tags={v: "v"}, edges={e: COLOR_FOCUS for e in inc},
                        emph=True, caption=self.formula(v)), len(V)
        if kind == "edge":
            names = list(self.ends)
            if not names:
                return dict(e=None, tags={}, edges={}, caption="no edges"), 0
            e = names[self.example_idx % len(names)]
            s = self.ends[e]
            return dict(e=e, tags={v: "end" for v in s}, edges={e: COLOR_FOCUS}, emph=True,
                        caption=f"{e} = {{{', '.join(map(str, sorted(s)))}}}: "
                                + ("a LOOP (one element)" if len(s) == 1
                                   else "two different ends, not a loop")
                                + f"   (edge {self.example_idx % len(names) + 1} of "
                                  f"{len(names)})"), len(names)
        if kind == "card":
            return dict(tags={v: f"#{i + 1}" for i, v in enumerate(V)}, edges={},
                        caption=f"Fintype.card (Fin 3) = {len(V)}  ≥  2"), 1
        if kind == "pair":
            k = self.example_idx % len(PAIRS)
            u, w = PAIRS[k]
            d = self.degs
            # gold = the edges counted in deg u and deg w; none for the impossible u = w
            inc = (set() if u == w else
                   set(incident_edges(self.ends, u)) | set(incident_edges(self.ends, w)))
            tags = {u: "u = w"} if u == w else {u: "u", w: "w"}
            cap = (f"case | {u}, {w}:  u = w, impossible because hne : u ≠ w" if u == w else
                   f"case | {u}, {w}:  deg u = {d[u]}, deg w = {d[w]}  →  "
                   + ("different ✓" if d[u] != d[w] else "EQUAL ✗")
                   + "   (gold: edges counted in deg u and deg w)")
            return dict(u=u, w=w, k=k, tags=tags, edges={e: COLOR_FOCUS for e in inc},
                        caption=cap), len(PAIRS)
        if kind == "simple":
            graphs = list(multigraphs_on(V, 1))
            k = self.example_idx % len(graphs)
            g = as_map(graphs[k])
            a, b = equal_degree_pairs(g)[0]
            return dict(graph=g, tags={a: "same", b: "same"}, edges={},
                        caption=f"simple graph {k + 1} of {len(graphs)}: vertices {a} and {b} "
                                f"both have degree {deg(g, a)}   (shown instead of ex8)"), \
                len(graphs)
        if kind == "claim":
            pairs = equal_degree_pairs(self.ends)
            cap = ("the claim promises u ≠ w with deg u = deg w ... but no such pair exists"
                   if not pairs else
                   f"in this edited graph the pair {pairs[0]} really has equal degrees")
            return dict(tags={v: "u?  w?" for v in V}, edges={}, caption=cap), 1
        raise ValueError(kind)

    # -- drawing ------------------------------------------------------------

    def redraw(self) -> None:
        s = STEPS[self.step]
        focus, n_examples = self.focus_info(s["focus"])
        shown = focus["graph"] if focus is not None and "graph" in focus else self.ends
        self._draw_graph(focus, shown)
        self._draw_sets(shown)
        self._draw_text(s, focus)
        self._draw_goal(s, focus)
        self._draw_code(s, focus)
        self.step_label.set_text(f"Step {self.step + 1} / {len(STEPS)}")
        self.btn_example.ax.set_visible(n_examples > 1)
        self.fig.canvas.draw_idle()

    def _draw_graph(self, focus: dict | None, shown: dict) -> None:
        ax = self.ax_graph
        ax.clear()
        if shown is not self.ends:
            caption = "A simple graph (not ex8)"
        else:
            caption = "The multigraph ex8" if not self.edited else "Your edited graph"
        caption += "   (" + fmt_edges(shown) + ")" if shown else "   (no edges)"
        edge_colors, emphasized, tags = {}, frozenset(), {}
        if focus is not None:
            edge_colors = focus["edges"]
            emphasized = frozenset(focus["edges"]) if focus.get("emph") else frozenset()
            tags = focus["tags"]
            caption = caption + "\n" + focus["caption"]
            if (self.selected is not None and "v" not in focus and "graph" not in focus
                    and STEPS[self.step]["focus"]):
                caption += "\nclicked: " + self.formula(self.selected)
        draw_edges(ax, shown, edge_colors, emphasized)
        draw_vertices(ax, shown, tags, dup=dup_vertices(shown), hidden=self.hidden)
        self.caption.set_text(textwrap.fill(caption.split("\n")[0], 95) +
                              ("\n" + caption.split("\n", 1)[1] if "\n" in caption else ""))
        frame(ax)

    def _draw_legend(self) -> None:
        handles = [
            Patch(facecolor=COLOR_VERTEX, edgecolor="#2A4F85", label="vertex"),
            Line2D([], [], color=COLOR_EDGE, linewidth=3, label="edge"),
            Line2D([], [], color=COLOR_PARALLEL, linewidth=3, label="parallel edges"),
            Line2D([], [], color=COLOR_LOOP, linewidth=3, linestyle="--",
                   label="loop (not allowed)"),
            Patch(facecolor="#E3F3E8", edgecolor=COLOR_OK, label="degree not shared"),
            Patch(facecolor="#FBE3E3", edgecolor=COLOR_WARN, label="degree shared"),
            Line2D([], [], color=COLOR_FOCUS, linewidth=4, label="gold: this step"),
        ]
        self.ax_legend.legend(handles=handles, loc="center", ncol=4, frameon=False,
                              fontsize=9.5, handlelength=2.2, columnspacing=1.4)

    def _draw_sets(self, shown: dict) -> None:
        ax = self.ax_sets
        ax.clear()
        ax.axis("off")
        ax.add_patch(plt.Rectangle((0, 0), 1, 1, transform=ax.transAxes, facecolor="#F7F7F7",
                                   edgecolor="#D0D0D0"))
        d = degrees(shown)
        multi = is_multigraph(shown)
        pairs = equal_degree_pairs(shown)

        def mark(ok: bool) -> tuple[str, str]:
            return ("✓", COLOR_OK) if ok else ("✗", COLOR_WARN)

        rows = [
            ("multigraph (no loops)?", *mark(multi)),
            (f"at least 2 vertices?  ({len(V)})", *mark(len(V) >= 2)),
            ("degrees", "  ".join(f"{v}:{'?' if self.hidden else d[v]}" for v in V),
             COLOR_TEXT),
            ("pairs u ≠ w with equal degree",
             "?" if self.hidden else
             (", ".join(f"({u},{w})" for u, w in pairs) if pairs else "none"), COLOR_TEXT),
        ]
        ax.text(0.04, 0.93, "Computed live from the edges", transform=ax.transAxes,
                fontsize=10.5, fontweight="bold", va="top")
        for i, (name, val, col) in enumerate(rows):
            y = 0.78 - i * 0.135
            ax.text(0.04, y, name, transform=ax.transAxes, fontsize=10, va="top",
                    fontweight="bold")
            ax.text(0.66, y, val, transform=ax.transAxes,
                    fontsize=14 if val in ("✓", "✗") else 10.5, va="top",
                    family="DejaVu Sans Mono", color=col, fontweight="bold")
        ce = is_counterexample(shown)
        if self.hidden and multi:
            ax.text(0.04, 0.17, "degrees hidden: predict them, then press 'Show degrees'",
                    transform=ax.transAxes, fontsize=10, fontweight="bold", va="top",
                    color="#5A4500")
            return
        if ce:
            verdict = "✓ a counterexample: the claim fails here"
        elif not multi:
            verdict = "✗ not a multigraph, so the claim says nothing"
        else:
            verdict = "✗ not a counterexample: a degree repeats"
        ax.text(0.04, 0.17, verdict, transform=ax.transAxes, fontsize=10.5, fontweight="bold",
                va="top", color=COLOR_OK if ce else COLOR_WARN)

    def _draw_text(self, s: dict, focus: dict | None) -> None:
        ax = self.ax_text
        ax.clear()
        ax.axis("off")
        math = s["math"](self, focus)
        if self.edited and s["part"] != "Part 1 · Graph basics":
            math = EDITED + math
        lean = s["lean"](self) if callable(s["lean"]) else s["lean"]
        def clean(t: str) -> str:
            # backticks are Markdown, not shown; ZWNJ stops the 'fl'/'fi' ligature (rfl!)
            return t.replace("`", "").replace("fl", "f\u200cl").replace("fi", "f\u200ci")

        blocks = [("What it means", clean(math)), ("In Lean", clean(lean))]

        # Shrink the font until everything fits the panel.
        height_pt = ax.get_position().height * self.fig.get_figheight() * 72
        for size in (11.5, 11, 10.5, 10, 9.5, 9, 8.5, 8):
            width = int(118 * 10 / size)
            wrapped = [(h, textwrap.wrap(t, width)) for h, t in blocks]
            n_lines = 1.3 + 1.9 + sum(1.25 + len(w) + 0.6 for _h, w in wrapped)
            if n_lines * size * 1.42 <= height_pt:
                break
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

    def _draw_goal(self, s: dict, focus: dict | None) -> None:
        """Lean's goal state before / after the tactics of this step (from the infoview)."""
        ax = self.ax_goal
        ax.clear()
        ax.axis("off")
        ax.add_patch(plt.Rectangle((0, 0), 1, 1, transform=ax.transAxes, facecolor="#F1F5FB",
                                   edgecolor="#B9C7DD"))
        ax.text(0.015, 0.93, "Lean's goal state  (⊢ = still to prove; names before ⊢ = facts "
                "we may use; 'no goals' = proved; abbreviated)",
                transform=ax.transAxes, fontsize=9.3, fontweight="bold", va="top",
                color="#2A4F85")
        if "goal" not in s and s["part"].startswith("Part 3"):
            body = ["This step looks back at the finished proof: after the last tactic there are",
                    "no goals left, so Lean has accepted the theorem."]
            family = None
        elif "goal" not in s:
            body = ["No proof is running in this step: it explains definitions.",
                    "Lean's goal state appears from step 5 (the theorem statement) on."]
            family = None
        else:
            body = []
            for ln in s["goal"](self, focus):
                for part in ln.split("\n"):
                    body += textwrap.wrap(part, 100, subsequent_indent="           ",
                                          drop_whitespace=False) or [""]
            family = "DejaVu Sans Mono"
            body.append("(… and parenthesized lists abbreviate long or earlier hypotheses; "
                        "Lean shows them in full.)")
        ax.text(0.015, 0.7, "\n".join(body), transform=ax.transAxes, fontsize=8.8,
                va="top", family=family, color=COLOR_TEXT, linespacing=1.35)

    def _draw_code(self, s: dict, focus: dict | None) -> None:
        """The Lean source, read from disk. Long sources scroll so that the highlighted
        lines are always visible; the header says which lines are shown."""
        ax = self.ax_code
        ax.clear()
        ax.axis("off")
        ax.add_patch(plt.Rectangle((0, 0), 1, 1, transform=ax.transAxes,
                                   facecolor=COLOR_CODE_BG, edgecolor="#D0D0D0"))
        src = self.lean[s["code"]]
        anchors = list(s["anchors"])
        if "dyn_anchor" in s and focus is not None:
            anchors.append(s["dyn_anchor"](focus))
        hl = highlighted_lines(src, anchors)
        fontsize = 9.6
        height_pt = ax.get_position().height * self.fig.get_figheight() * 72
        line = fontsize * 1.42 / height_pt  # one code line, in axes fraction
        top = 0.9
        n_fit = int((top - 0.02) / line)
        if len(src) <= n_fit:
            first = 0
        else:
            lo, hi = (min(hl), max(hl)) if hl else (0, 0)
            first = max(0, min(len(src) - n_fit, (lo + hi) // 2 - n_fit // 2))
            if hl and hi - lo >= n_fit:
                first = lo
        shown = src[first:first + n_fit]
        name = ("GraphCh10/Exercises/Supp08.lean" if s["code"] == "proof"
                else "GraphCh10/Definitions.lean + DefinitionTests.lean")
        rng = ("" if len(shown) == len(src) else
               f"; lines {first + 1}–{first + len(shown)} of {len(src)}")
        ax.text(0.015, 0.975, f"Lean source: {name}  (from disk; gold = this step{rng};  "
                "⟨ ⟩ = angle brackets)",
                transform=ax.transAxes, fontsize=8.6, fontweight="bold", va="top",
                color="#555555")
        for j, ln in enumerate(shown):
            i = first + j
            y = top - j * line
            if i in hl:
                ax.add_patch(plt.Rectangle((0.008, y - line * 0.98), 0.984, line,
                                           transform=ax.transAxes, facecolor=COLOR_CODE_HL,
                                           edgecolor=COLOR_FOCUS, linewidth=1))
            ax.text(0.015, y, ln if ln else " ", transform=ax.transAxes, va="top",
                    fontsize=fontsize, family="DejaVu Sans Mono",
                    color=COLOR_TEXT if i in hl or not ln.strip().startswith("--") else "#6A737D",
                    fontweight="bold" if i in hl else "normal")


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


def self_test(ex: Explorer, outdir: Path) -> None:
    outdir.mkdir(parents=True, exist_ok=True)
    # 0. Degrees start hidden (predict first); entering step 4 reveals them.
    assert ex.hidden and not ex.revealed
    # 1. Every step renders, for every example the step offers; exactly the right code lines
    #    are highlighted (including the per-case line of the `match`).
    for k, s in enumerate(STEPS):
        ex.enter_step(k)
        _f, n = ex.focus_info(s["focus"])
        for _ in range(max(n, 1)):
            ex.redraw()
            f, _n = ex.focus_info(s["focus"])
            if "dyn_anchor" in s:
                hits = [ln for ln in ex.lean["proof"] if s["dyn_anchor"](f) in ln]
                assert len(hits) == 1
            if s["focus"] == "pair":  # goal box follows the Lean infoview for this case
                g = "\n".join(s["goal"](ex, f))
                assert f"hne : {f['u']} ≠ {f['w']}" in g
                if f["u"] == f["w"]:
                    assert f["edges"] == {} and "absurd" in g
                else:
                    assert f"⊢ {EX8_DEG[f['u']]} ≠ {EX8_DEG[f['w']]}" in g
            ex.next_example()
        ex.enter_step(k)
        ex.fig.savefig(outdir / f"step_{k + 1:02d}.png", dpi=90)
    # 1b. The `have … := by` steps highlight their whole block, including `decide`.
    for title in ("have hMulti", "have hCard", "have hDeg"):
        s = next(st for st in STEPS if st["title"].startswith(title))
        src = ex.lean["proof"]
        hl = highlighted_lines(src, s["anchors"])
        assert any(src[i].strip() == "decide" for i in hl), f"{title}: decide not highlighted"
    # 1c. Every proof step has a goal box; the case (0, 1) matches the Lean infoview
    #     (`⊢ 1 ≠ 3` after `rw [h0, h1]`, captured with lean_goal).
    assert all("goal" in st for st in STEPS if st["part"].startswith("Part 2"))
    pair_step = next(st for st in STEPS if st["focus"] == "pair")
    assert "after rw [h0, h1]:     ⊢ 1 ≠ 3" in pair_step["goal"](ex, dict(u=0, w=1))
    # 2. Simulated clicks on the Next / Previous buttons move the walkthrough.
    ex.enter_step(0)
    _click(ex, ex.btn_next)
    assert ex.step == 1, "Next button did not advance"
    _click(ex, ex.btn_prev)
    assert ex.step == 0, "Previous button did not go back"
    # 3. Clicking a vertex on the degree step selects it as the example.
    deg_step = next(i for i, s in enumerate(STEPS) if s["focus"] == "degree")
    ex.enter_step(deg_step)
    _press(ex.fig, ex.ax_graph, *POS[1])
    f, _n = ex.focus_info("degree")
    assert f["v"] == 1 and set(f["edges"]) == {"e0", "e1", "e2"}
    ex.fig.savefig(outdir / "click_vertex_1.png", dpi=90)
    # 4. Editing: removing a parallel copy of {1,2} makes degrees repeat (1, 2, 1).
    try_step = next(i for i, s in enumerate(STEPS) if s["title"].startswith("Try it"))
    ex.enter_step(try_step)
    assert is_counterexample(ex.ends) and not ex.edited
    _click(ex, ex.edit_buttons["-12"])
    assert ex.degs == {0: 1, 1: 2, 2: 1} and equal_degree_pairs(ex.ends) == [(0, 2)]
    assert ex.edited and not is_counterexample(ex.ends)
    ex.fig.savefig(outdir / "edit_remove_parallel.png", dpi=90)
    # ... adding {0,2} as well: degrees 2, 2, 2.
    _click(ex, ex.edit_buttons["+02"])
    assert ex.degs == {0: 2, 1: 2, 2: 2}
    # ... a loop at 0 counts twice and breaks the multigraph hypothesis.
    _click(ex, ex.btn_loop)
    assert ex.degs[0] == 4 and not is_multigraph(ex.ends)
    ex.fig.savefig(outdir / "edit_loop.png", dpi=90)
    # ... edited graphs still render on every proof step (with the warning).
    for k in range(len(STEPS)):
        ex.enter_step(k)
    _click(ex, ex.btn_reset)
    assert ex.ends == EX8_ENDS and is_counterexample(ex.ends) and not ex.edited
    # 4b. Predict-then-check: hiding the degrees hides every number, showing restores them.
    ex.enter_step(deg_step)
    _click(ex, ex.btn_hide)
    assert ex.hidden and "?" in ex.formula(1) and ex.btn_hide.label.get_text() == "Show degrees"
    ex.fig.savefig(outdir / "hidden_degrees.png", dpi=90)
    _click(ex, ex.btn_hide)
    assert not ex.hidden and ex.formula(1).endswith("= 3")
    # 4b'. Edits keep the names of untouched edges: a new edge is appended, a loop is not e0.
    _click(ex, ex.edit_buttons["+02"])
    assert ex.ends["e0"] == sym2(0, 1) and ex.ends["e3"] == sym2(0, 2)
    _click(ex, ex.edit_buttons["-02"])
    assert ex.ends == EX8_ENDS
    # 4b''. Step 14 browses all 8 simple graphs on 3 vertices, each repeating a degree.
    ex.enter_step(len(STEPS) - 1)
    for _ in range(8):
        f, n = ex.focus_info("simple")
        assert n == 8 and equal_degree_pairs(f["graph"]) and is_multigraph(f["graph"])
        ex.next_example()
    ex.fig.savefig(outdir / "simple_graphs.png", dpi=90)
    assert ex.ends == EX8_ENDS  # browsing does not change the user's graph
    # 4c. Loops at vertices 1 and 2 also count twice.
    _click(ex, ex.loop_buttons[1])
    _click(ex, ex.loop_buttons[2])
    assert ex.degs == {0: 1, 1: 5, 2: 4} and not is_multigraph(ex.ends)
    ex.fig.savefig(outdir / "loops_1_2.png", dpi=90)
    _click(ex, ex.btn_reset)
    # 5. Another counterexample can be built: {0,1}, {0,2}, {0,2}, {1,2}, {1,2}, {1,2}.
    #    Degrees 3, 4, 5 -- all different.
    _click(ex, ex.edit_buttons["+02"])
    _click(ex, ex.edit_buttons["+02"])
    _click(ex, ex.edit_buttons["+12"])
    assert ex.degs == {0: 3, 1: 4, 2: 5} and is_counterexample(ex.ends)
    ex.fig.savefig(outdir / "edit_other_counterexample.png", dpi=90)
    # 6. Empty graph: all degrees 0; the add-limit holds at 3 copies.
    for key in ("01", "02", "12"):
        for _ in range(4):
            _click(ex, ex.edit_buttons["-" + key])
    assert ex.ends == {} and ex.degs == {0: 0, 1: 0, 2: 0}
    for k in range(len(STEPS)):
        ex.enter_step(k)
    for _ in range(5):
        _click(ex, ex.edit_buttons["+01"])
    assert len(ex.ends) == 3
    _click(ex, ex.btn_reset)
    assert ex.ends == EX8_ENDS
    print(f"Explorer self-test passed: {len(STEPS)} steps rendered, buttons, vertex clicks "
          f"and graph editing work; snapshots in {outdir}")


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
    print("ex8 (parsed from DefinitionTests.lean):", fmt_edges(EX8_ENDS))
    print("Degrees:", ", ".join(f"deg({v}) = {EX8_DEG[v]}" for v in V),
          " (match `have hDeg` in Supp08.lean)")
    print("Multigraph: yes;  vertices: 3 ≥ 2;  pairs u ≠ w with equal degree: none")
    print(f"All assertions passed (counterexample, 9 match cases, "
          f"{stats['n_simple']:,} simple graphs, minimality on 2 and 3 vertices).")

    out = Path(__file__).resolve().parent / "supp08.png"
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
