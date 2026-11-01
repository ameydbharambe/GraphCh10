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

Explorer controls:
    click a vertex          show how its degree is counted (its incident edges turn gold)
    − / +  buttons          remove / add a parallel copy of the edge {0,1}, {0,2} or {1,2}
    Loop at 0               add or remove a loop at vertex 0 (then it is no longer a multigraph)
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
LOOP_DIR: dict[int, tuple[float, float]] = {0: (-1.0, 0.0), 1: (-0.8, 0.6), 2: (1.0, 0.0)}

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
    return (k - (m - 1) / 2) * 0.42


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
                  r: float = NODE_R, fontsize: float = 15) -> None:
    """Vertices with their names; `badges` adds a 'deg = k' label; `dup` vertices (sharing a
    degree with another vertex) get a red badge; `tags` adds a gold halo + tag."""
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
            bad = v in dup
            ax.text(x + dx, y + dy, f"deg = {deg(ends_map, v)}", ha="center", va="center",
                    fontsize=fontsize * 0.72, fontweight="bold", zorder=6,
                    color=COLOR_WARN if bad else "#1B4D2C",
                    bbox=dict(boxstyle="round,pad=0.25", fc="#FBE3E3" if bad else "#E3F3E8",
                              ec=COLOR_WARN if bad else COLOR_OK))
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
             "Run  python visualizations/supp08.py  for the interactive walkthrough.",
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
        ax.set_title(f"deg {pairs[0][0]} = deg {pairs[0][1]}", fontsize=9.5, color=COLOR_WARN,
                     pad=2)
    ax0 = fig.add_subplot(gs[1, 2:], frameon=False)
    ax0.set_xticks([])
    ax0.set_yticks([])
    ax0.set_title("Why the parallel edge matters: all 8 SIMPLE graphs on 3 vertices",
                  fontsize=13, fontweight="bold", pad=22)
    ax0.text(0.5, 1.015, "without parallel edges every one of them repeats a degree (red); "
             f"checked for all {stats['n_simple']:,} simple graphs on 2 to 5 vertices",
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
             f"  counterexample has ≥ 3 edges ({stats['n_three']} with exactly 3): ex8 is minimal",
             "• every simple graph on 2..5 vertices repeats a degree"]
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
    return ", ".join(f"deg({v}) = {d[v]}" for v in V)


STEPS: list[dict] = [
    dict(
        part="Part 1 · Graph basics", title="Vertices and edges", code="defs",
        anchors=["structure UGraph", "ends : E → Sym2 V", "def ex8"], focus=None,
        math=lambda ex, f: (
            "A graph has vertices (the blue circles 0, 1, 2) and edges (the lines e0, e1, "
            "e2). Each edge has a set of endpoints: e0 joins 0 and 1, while e1 and e2 both "
            "join 1 and 2. This is the graph the Lean proof uses, called ex8. It is read "
            "straight from the Lean file, not typed in by hand."),
        lean=("`structure UGraph (V E)` has one field, `ends : E → Sym2 V`, which gives every "
              "edge its set of endpoints. In `ex8` the vertices are `Fin 3` = {0, 1, 2} and "
              "the edges are also `Fin 3`. `fun e => if e = 0 then s(0, 1) else s(1, 2)` "
              "says: edge 0 has ends {0, 1}; every other edge (1 and 2) has ends {1, 2}."),
    ),
    dict(
        part="Part 1 · Graph basics", title="Parallel edges and loops: what a multigraph is",
        code="defs", anchors=["def IsLoop", "def IsMultigraph"], focus="parallel",
        math=lambda ex, f: (
            "Two different edges with the same endpoints are called parallel (or multiple) "
            "edges: here e1 and e2 (gold, orange elsewhere). A loop is an edge from a vertex "
            "to itself. A multigraph may have parallel edges but NO loops. So ex8 is a "
            "multigraph. Simple graphs allow neither, so ex8 is not a simple graph."),
        lean=("`def IsLoop (e : E) : Prop := (G.ends e).IsDiag`: the endpoint set has one "
              "element, like s(v, v). `def IsMultigraph : Prop := ∀ e : E, ¬ G.IsLoop e`: "
              "no edge is a loop. Nothing forbids parallel edges, because two edges may have "
              "the same `ends`."),
    ),
    dict(
        part="Part 1 · Graph basics", title="The degree of a vertex",
        code="defs", anchors=["def Incident", "def deg", "G.Incident e v)).card",
                              "s(v, v))).card"], focus="degree",
        math=lambda ex, f: (
            "The degree of v is the number of edges touching v, with loops counted twice. "
            f"Gold: the edges counted for v = {f['v']}. {deg_formula(ex.ends, f['v'])}. "
            "Each parallel edge counts separately, so the two copies of {1, 2} give vertex 1 "
            "two of its three. Click a vertex or press 'Next example'."),
        lean=("`deg v` adds two counts. `(Finset.univ.filter (fun e => G.Incident e v)).card` "
              "is the number of edges e with v ∈ ends e. The second summand counts the "
              "loops at v once more. `Finset.univ` is the finite set of all edges, which "
              "is why `[Fintype E]` is needed."),
    ),
    dict(
        part="Part 1 · Graph basics", title="Try it: edit the graph",
        code="defs", anchors=["def deg"], focus=None,
        math=lambda ex, f: (
            "Use the − / + buttons to remove or add copies of an edge, and watch the "
            "degrees and the panel below the graph update. Try removing one copy of {1, 2}: "
            "the degrees become 1, 2, 1 and a degree repeats. Try adding a loop at 0: the "
            "graph stops being a multigraph. Can you find a different counterexample? "
            f"Right now: {_deg_list(ex)}."),
        lean=("Nothing in this step is Lean: the panel recomputes `IsMultigraph` and `deg` "
              "from the edges, exactly as the definitions say. 'Reset to ex8' brings back "
              "the graph used by the proof."),
    ),
    dict(
        part="Part 1 · Graph basics", title="The claim, and how to disprove it",
        code="proof", anchors=["¬ ∀ (V E : Type)", "G.IsMultigraph → 2 ≤ Fintype.card V →",
                               "∃ u w : V, u ≠ w ∧ G.deg u = G.deg w"], focus=None,
        math=lambda ex, f: (
            "The claim says: EVERY finite multigraph with at least two vertices has two "
            "different vertices of the same degree. A 'for every' statement is false as soon "
            "as ONE case breaks it. Such a case is called a counterexample. ex8 is one: it "
            "is a finite multigraph, it has 3 ≥ 2 vertices, and its degrees 1, 3, 2 are all "
            "different. (Without parallel edges the claim would be true; see Part 3.)"),
        lean=("We prove the NEGATION `¬ ∀ …` of the claim. `∀ (V E : Type)` ranges over all "
              "vertex and edge types; `[Fintype V] [Fintype E]` say they are finite, and "
              "`[DecidableEq V]` lets Lean compute degrees. `→` chains the hypotheses, "
              "and `∃ u w : V, u ≠ w ∧ …` is the conclusion we will show fails for ex8."),
    ),
    dict(
        part="Part 2 · The Lean proof", title="intro claim: assume the claim",
        code="proof", anchors=["intro claim", "assume, for contradiction"], focus=None,
        math=lambda ex, f: (
            "To show a statement is false, assume it is true and derive a contradiction. "
            "So suppose every finite multigraph with at least two vertices has two vertices "
            "of equal degree. Then use this assumption on ex8 and see it fail."),
        lean=("In Lean, `¬ P` is defined as `P → False`. So `intro claim` assumes "
              "`claim : ∀ V E …, …` and the goal becomes `False`. The rest of the proof "
              "builds a proof of `False` from `claim`."),
    ),
    dict(
        part="Part 2 · The Lean proof", title="have hMulti: ex8 is a multigraph",
        code="proof", anchors=["have hMulti", "has no loops, so it is a multigraph",
                               "unfold UGraph.IsMultigraph UGraph.IsLoop"], focus="edge",
        math=lambda ex, f: (
            "Check every edge: it must join two DIFFERENT vertices. Right now the graph has "
            "no edges at all, so there is no loop and it is a multigraph."
        ) if f["e"] is None else (
            "Check every edge: it must join two DIFFERENT vertices. "
            f"Gold: {f['e']} = {{{', '.join(map(str, sorted(ex.ends[f['e']])))}}}, "
            f"{'a loop!' if is_loop(ex.ends, f['e']) else 'two different vertices, so not a loop'}. "
            f"Is the whole graph a multigraph? {'yes' if is_multigraph(ex.ends) else 'NO'}. "
            "'Next example' shows the other edges."),
        lean=("`have hMulti : ex8.IsMultigraph := by …` proves a fact and names it. `unfold` "
              "replaces `IsMultigraph` and `IsLoop` by their definitions. The goal becomes "
              "`∀ e : Fin 3, ¬ (ex8.ends e).IsDiag`, which talks about only finitely many edges. "
              "`decide` then checks all three edges by computation, and Lean's kernel "
              "re-checks the result."),
    ),
    dict(
        part="Part 2 · The Lean proof", title="have hCard: at least two vertices",
        code="proof", anchors=["have hCard", "rw [Fintype.card_fin]",
                               "it has three vertices, so at least two"], focus="card",
        math=lambda ex, f: (
            "Count the vertices: 0, 1, 2, so there are 3 of them, and 2 ≤ 3. "
            "So ex8 satisfies the second hypothesis of the claim."),
        lean=("`Fintype.card (Fin 3)` is the number of elements of `Fin 3`. "
              "`rw [Fintype.card_fin]` rewrites it to `3` using the library lemma "
              "`Fintype.card (Fin n) = n`. The goal is now `2 ≤ 3`, and `decide` checks "
              "that by computation."),
    ),
    dict(
        part="Part 2 · The Lean proof", title="have hDeg: the three degrees",
        code="proof", anchors=["have hDeg", "its degrees are deg(0) = 1"], focus="degree",
        math=lambda ex, f: (
            f"Count the edges touching each vertex. {deg_formula(ex.ends, f['v'])}. "
            "For ex8: deg(0) = 1, deg(1) = 3 (e0 plus both parallel edges), deg(2) = 2. "
            "'Next example' or a click shows the other vertices."),
        lean=("The statement `ex8.deg 0 = 1 ∧ ex8.deg 1 = 3 ∧ ex8.deg 2 = 2` joins three "
              "equations with `∧` (and). Each `deg` is a size of a filtered finite set of "
              "edges, so `decide` can count it directly. No graph theory is needed, only "
              "computation, which the kernel checks."),
    ),
    dict(
        part="Part 2 · The Lean proof", title="have hDistinct: different vertices, different degrees",
        code="proof", anchors=["have hDistinct", "intro u w hne", "obtain ⟨h0, h1, h2⟩ := hDeg",
                               "match u, w with"],
        dyn_anchor=lambda f: f"| {f['u']}, {f['w']} =>", focus="pair",
        math=lambda ex, f: (
            "Check every pair (u, w) of vertices. "
            + (f"Here u = w = {f['u']}: this case is impossible, because we assumed u ≠ w."
               if f['u'] == f['w'] else
               f"Here u = {f['u']}, w = {f['w']}: deg u = {ex.degs[f['u']]}, "
               f"deg w = {ex.degs[f['w']]}, "
               + ("different. ✓" if ex.degs[f['u']] != ex.degs[f['w']]
                  else "EQUAL, so this graph is not a counterexample.")) +
            f" (case {f['k'] + 1} of 9; 'Next example' shows the next case.)"),
        lean=("`intro u w hne` takes vertices u, w and `hne : u ≠ w`. `obtain ⟨h0, h1, h2⟩ := "
              "hDeg` splits the ∧ into three equations. `match u, w with` lists all 9 cases. "
              "When u = w, `absurd rfl hne` notes that `rfl : u = u` contradicts `hne`. "
              "Otherwise `rw [h0, h1]` turns `ex8.deg 0 ≠ ex8.deg 1` into `1 ≠ 3`, and "
              "`decide` checks it."),
    ),
    dict(
        part="Part 2 · The Lean proof", title="obtain … := claim … ex8: use the claim on ex8",
        code="proof", anchors=["obtain ⟨u, w, hne, hEq⟩ := claim", "applied to `ex8`"],
        focus="claim",
        math=lambda ex, f: (
            "The assumed claim holds for EVERY multigraph, so in particular for ex8. "
            "We have just checked its hypotheses (hMulti, hCard). So the claim promises "
            "two vertices u ≠ w with deg u = deg w. The question marks show what it promises. "
            "But ex8 has no such pair."),
        lean=("`claim (Fin 3) (Fin 3) ex8 hMulti hCard` plugs ex8 into the ∀. The `[Fintype …]` "
              "and `[DecidableEq …]` arguments are found automatically, and the two "
              "hypotheses are given as proofs. The result is `∃ u w, u ≠ w ∧ ex8.deg u = "
              "ex8.deg w`. `obtain ⟨u, w, hne, hEq⟩` names its parts."),
    ),
    dict(
        part="Part 2 · The Lean proof", title="exact hDistinct u w hne hEq: contradiction ∎",
        code="proof", anchors=["-- contradiction", "exact hDistinct u w hne hEq"], focus=None,
        math=lambda ex, f: (
            "hDistinct says the two degrees are different; the claim says they are equal. "
            "Both cannot hold, so the assumption was false: the claim is disproved. "
            "ex8 is a finite multigraph with at least two vertices in which all degrees are "
            "different."),
        lean=("`hDistinct u w hne : ex8.deg u ≠ ex8.deg w`, and `≠` means `(… = …) → False`. "
              "Applying it to `hEq : ex8.deg u = ex8.deg w` gives `False`, which is the goal. "
              "`exact` closes it, and Lean's kernel re-checks the whole proof."),
    ),
    dict(
        part="Part 3 · Why this works", title="One counterexample is a complete proof",
        code="proof", anchors=[], focus=None,
        math=lambda ex, f: (
            "In Exercise 9(a) a picture could only illustrate a 'for every' theorem. Here "
            "the situation is reversed: one picture of ex8 really DISPROVES the claim. "
            "Why are parallel edges essential? Without them, a vertex adjacent to all others "
            "and a vertex with no edges cannot both exist, so some degree must repeat. "
            f"This script checked all {ex.stats['n_simple']:,} simple graphs on 2 to 5 "
            "vertices: each one repeats a degree. With 2 vertices any multigraph has equal "
            "degrees, and every 3-vertex counterexample needs at least 3 edges, so ex8 is "
            "as small as possible."),
        lean=("`#print axioms GraphCh10.supp08` reports only Lean's standard axioms propext, "
              "Classical.choice and Quot.sound: no `sorry` and no project axioms. Every "
              "`decide` is a computation checked by the kernel; no `native_decide` is used."),
    ),
]

PAIR_KEYS = [("01", 0, 1), ("02", 0, 2), ("12", 1, 2)]


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
        self.ax_text = self.fig.add_axes([0.505, 0.615, 0.48, 0.305])
        self.ax_code = self.fig.add_axes([0.505, 0.105, 0.48, 0.5])
        for ax in (self.ax_legend, self.ax_edit, self.ax_sets, self.ax_text, self.ax_code):
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
        self.btn_loop = button([0.017, 0.085, 0.153, 0.035], "Loop at 0: add / remove",
                               lambda _e: self.toggle_loop(0), size=9.5)
        self.btn_reset = button([0.017, 0.04, 0.153, 0.035], "Reset to ex8",
                                lambda _e: self.reset(), color="#E3EEDF", size=9.5)

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
        """Every walkthrough anchor must match exactly one line of the real Lean source."""
        for s in STEPS:
            lines = self.lean[s["code"]]
            anchors = list(s["anchors"])
            if "dyn_anchor" in s:
                anchors += [s["dyn_anchor"](dict(u=u, w=w)) for u, w in PAIRS]
            for anchor in anchors:
                n = sum(anchor in ln for ln in lines)
                assert n == 1, f"anchor {anchor!r} matches {n} lines of the {s['code']} source"

    @property
    def degs(self) -> dict[int, int]:
        return degrees(self.ends)

    @property
    def edited(self) -> bool:
        return sorted(self.ends.values(), key=sorted) != sorted(EX8_ENDS.values(), key=sorted)

    def _set_edges(self, ends_list: list[frozenset[int]]) -> None:
        self.ends = as_map(sorted(ends_list, key=lambda s: (len(s), sorted(s))))
        self.redraw()

    def add_edge(self, a: int, b: int) -> None:
        if sum(s == sym2(a, b) for s in self.ends.values()) < 3:  # at most 3 parallel copies
            self._set_edges([*self.ends.values(), sym2(a, b)])

    def remove_edge(self, a: int, b: int) -> None:
        lst = list(self.ends.values())
        if sym2(a, b) in lst:
            lst.remove(sym2(a, b))
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

    def go(self, delta: int) -> None:
        self.enter_step(max(0, min(len(STEPS) - 1, self.step + delta)))

    def next_example(self) -> None:
        self.example_idx += 1
        self.redraw()

    def enter_step(self, k: int) -> None:
        self.step, self.example_idx = k, 0
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
            self.example_idx = V.index(v)
        self.redraw()

    def _on_key(self, event) -> None:
        if event.key == "right":
            self.go(+1)
        elif event.key == "left":
            self.go(-1)

    # -- what to highlight --------------------------------------------------

    def focus_info(self, kind: str | None) -> tuple[dict | None, int]:
        """What the current step highlights in gold / bold. Returns (info, #examples)."""
        sel = getattr(self, "selected", None)
        if kind is None:
            if sel is None:
                return None, 0
            inc = incident_edges(self.ends, sel)
            return dict(tags={sel: "v"}, edges={e: COLOR_FOCUS for e in inc},
                        caption=deg_formula(self.ends, sel)), 0
        if kind == "parallel":
            par = [e for e in self.ends if default_edge_color(self.ends, e) == COLOR_PARALLEL]
            return dict(tags={}, edges={e: COLOR_FOCUS for e in par},
                        caption=("gold: parallel edges " + ", ".join(par)) if par
                        else "no parallel edges right now"), 1
        if kind == "degree":
            v = V[self.example_idx % len(V)]
            inc = incident_edges(self.ends, v)
            return dict(v=v, tags={v: "v"}, edges={e: COLOR_FOCUS for e in inc},
                        emph=True, caption=deg_formula(self.ends, v)), len(V)
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
            inc = set(incident_edges(self.ends, u)) | set(incident_edges(self.ends, w))
            tags = {u: "u = w"} if u == w else {u: "u", w: "w"}
            cap = (f"case | {u}, {w}:  u = w, excluded by hne : u ≠ w" if u == w else
                   f"case | {u}, {w}:  deg u = {d[u]}, deg w = {d[w]}  →  "
                   + ("different ✓" if d[u] != d[w] else "EQUAL ✗"))
            return dict(u=u, w=w, k=k, tags=tags, edges={e: COLOR_FOCUS for e in inc},
                        caption=cap), len(PAIRS)
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
        self._draw_graph(focus)
        self._draw_sets()
        self._draw_text(s, focus)
        self._draw_code(s, focus)
        self.step_label.set_text(f"Step {self.step + 1} / {len(STEPS)}")
        self.btn_example.ax.set_visible(n_examples > 1)
        self.fig.canvas.draw_idle()

    def _draw_graph(self, focus: dict | None) -> None:
        ax = self.ax_graph
        ax.clear()
        caption = "The multigraph ex8" if not self.edited else "Your edited graph"
        caption += "   (" + fmt_edges(self.ends) + ")" if self.ends else "   (no edges)"
        edge_colors, emphasized, tags = {}, frozenset(), {}
        if focus is not None:
            edge_colors = focus["edges"]
            emphasized = frozenset(focus["edges"]) if focus.get("emph") else frozenset()
            tags = focus["tags"]
            caption = caption + "\n" + focus["caption"]
        draw_edges(ax, self.ends, edge_colors, emphasized)
        draw_vertices(ax, self.ends, tags, dup=dup_vertices(self.ends))
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

    def _draw_sets(self) -> None:
        ax = self.ax_sets
        ax.clear()
        ax.axis("off")
        ax.add_patch(plt.Rectangle((0, 0), 1, 1, transform=ax.transAxes, facecolor="#F7F7F7",
                                   edgecolor="#D0D0D0"))
        d = self.degs
        multi = is_multigraph(self.ends)
        pairs = equal_degree_pairs(self.ends)

        def mark(ok: bool) -> tuple[str, str]:
            return ("✓", COLOR_OK) if ok else ("✗", COLOR_WARN)

        rows = [
            ("multigraph (no loops)?", *mark(multi)),
            (f"at least 2 vertices?  ({len(V)})", *mark(len(V) >= 2)),
            ("degrees", "  ".join(f"{v}:{d[v]}" for v in V), COLOR_TEXT),
            ("pairs u ≠ w with equal degree",
             ", ".join(f"({u},{w})" for u, w in pairs) if pairs else "none", COLOR_TEXT),
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
        ce = is_counterexample(self.ends)
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
        blocks = [("What it means", math), ("In Lean", s["lean"])]

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

    def _draw_code(self, s: dict, focus: dict | None) -> None:
        ax = self.ax_code
        ax.clear()
        ax.axis("off")
        ax.add_patch(plt.Rectangle((0, 0), 1, 1, transform=ax.transAxes,
                                   facecolor=COLOR_CODE_BG, edgecolor="#D0D0D0"))
        src = self.lean[s["code"]]
        anchors = list(s["anchors"])
        if "dyn_anchor" in s and focus is not None:
            anchors.append(s["dyn_anchor"](focus))
        name = ("GraphCh10/Exercises/Supp08.lean" if s["code"] == "proof"
                else "GraphCh10/Definitions.lean + DefinitionTests.lean")
        ax.text(0.015, 0.975, f"Lean source: {name}  (read from disk; highlighted = this step)",
                transform=ax.transAxes, fontsize=9.5, fontweight="bold", va="top",
                color="#555555")
        n = max(len(src), 22)
        step_y = 0.89 / n
        fontsize = 9 if n <= 30 else 8.4
        for i, ln in enumerate(src):
            hl = any(a in ln for a in anchors)
            y = 0.925 - i * step_y
            if hl:
                ax.add_patch(plt.Rectangle((0.008, y - step_y * 0.95), 0.984, step_y * 0.98,
                                           transform=ax.transAxes, facecolor=COLOR_CODE_HL,
                                           edgecolor=COLOR_FOCUS, linewidth=1))
            ax.text(0.015, y, ln if ln else " ", transform=ax.transAxes, va="top",
                    fontsize=fontsize, family="DejaVu Sans Mono",
                    color=COLOR_TEXT if hl or not ln.strip().startswith("--") else "#6A737D",
                    fontweight="bold" if hl else "normal")


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
            ex.next_example()
        ex.enter_step(k)
        ex.fig.savefig(outdir / f"step_{k + 1:02d}.png", dpi=90)
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
