"""Visualization for Rosen Ch. 10, Supplementary Exercise 39: a graph with a cut edge is not orientable.

    "Show that a graph is not orientable if it has a cut edge."

An EDUCATIONAL COMPANION to the Lean theorem `GraphCh10.supp39` (GraphCh10/Exercises/Supp39.lean),
for students who are new to Lean 4 and to graph theory. It has two parts:

1. A static summary figure (visualizations/supp39.png).
2. An interactive explorer: an example graph with a cut edge e₀, one attempt at directing all of its
   edges (click an edge to reverse it, or flip e₀), a chosen vertex x (click a vertex), the
   directed path from x to the tail a of e₀ (when one exists), and the conversion of that path,
   edge by edge, into an undirected path in G − e₀, exactly as the Lean helper lemma does it.
   Previous / Next steps through the actual Lean proof; every step explains the graph theory and
   the Lean syntax separately and highlights the matching Lean lines (read from disk at runtime).

MATHEMATICAL HONESTY. The proof is by contradiction: it SUPPOSES an orientation exists (a choice of
directions that is strongly connected) and derives a contradiction. Such an orientation does not
exist, so it can never be drawn. What the explorer draws is always a REAL choice of directions, and
it shows where that choice fails: the vertices on the far side of e₀ have no directed path to a.
The helper lemma itself needs no "suppose": it holds for every choice of directions, so the
explorer runs it on real directed paths. Every picture is one example; the general statement is
established by the Lean proof, not by this script.

The graph model follows GraphCh10/Definitions.lean:

* `UGraph V E` with `ends : E → Sym2 V`        -- `ends[e]` is a frozenset {u, w} (Python dict).
  Edges of the examples are named by their endpoints, e.g. "{2,3}" (the examples are simple).
* `UGraph.Path x y` (`nil`, `cons e h p`)      -- a list of steps (e, from, to); [] is `Path.nil`.
* `Connected := ∀ x y, Nonempty (G.Path x y)`   -- `connected`.
* `deleteEdge G e₀` (edges `{e // e ≠ e₀}`)     -- `delete_edge`: the same dict without e₀.
* `IsCutEdge G e := ¬ (G.deleteEdge e).Connected` -- `is_cut_edge` (literal "G − e disconnected").
* `DGraph V E` with `ends : E → V × V`          -- an orientation dict o[e] = (tail, head).
* `DGraph.Path x y`                             -- `dpath`: steps (e, u, w) with o[e] == (u, w).
* `StronglyConnected := ∀ x y, Nonempty (Path x y)` -- `strongly_connected`.
* `IsOrientation G o := (∀ e, s((o e).1, (o e).2) = G.ends e) ∧ (DGraph.mk o).StronglyConnected`
                                                -- `directions_ok` and `is_orientation`.
* `Orientable G := ∃ o, G.IsOrientation o`      -- `orientable` (tries all 2^m choices).
* `Supp39.path_avoiding_of_dpath_to_tail`       -- `lemma_convert`, the same recursion.

Every path, component, cut-edge status and strong-connectivity status shown is COMPUTED from these
functions; none is hardcoded. Vertex positions on the screen are the only hand-chosen data.

Run (from the project root):
    python -m pip install networkx matplotlib
    python visualizations/supp39.py              # save the PNG, then open the explorer
    python visualizations/supp39.py --static     # only checks + PNG (no window)
    python visualizations/supp39.py --snapshots DIR
        # headless self-test: drives the explorer through every walkthrough step,
        # simulates mouse clicks / buttons / keys, and saves one PNG per step into DIR

Explorer controls:
    click a vertex          choose the vertex x (start of the directed path to a)
    click an edge           reverse its direction (clicking e₀ also swaps a and b)
    Flip e₀                 reverse the cut edge e₀: its tail a and head b swap
    Next e₀                 choose another cut edge as e₀ (in the contrast graph: any edge)
    Next graph              two triangles + bridge / triangle with a tail / 6-cycle (contrast)
    Random arrows           a random choice of directions
    Reset                   the graph's starting directions, e₀ and x
    Path: shortest / via e₀ use the shortest directed path x → a, or one that passes through
                            e₀ (exists only when the head b can get back to a)
    Walk the path ▶         convert the directed path one edge at a time (as the lemma does)
    ◀ Previous / Next ▶     move through the walkthrough (also ← / → keys)
"""

from __future__ import annotations

import argparse
import random
import sys
import textwrap
from collections import deque
from itertools import combinations, product
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
from matplotlib.patches import Circle, FancyArrowPatch, Patch
from matplotlib.widgets import Button

PROJECT_ROOT = Path(__file__).resolve().parent.parent
PROOF_FILE = PROJECT_ROOT / "GraphCh10" / "Exercises" / "Supp39.lean"
DEFS_FILE = PROJECT_ROOT / "GraphCh10" / "Definitions.lean"
LEMMAS_FILE = PROJECT_ROOT / "GraphCh10" / "Lemmas.lean"

# The statements approved by the project owner (checked against the Lean file).
APPROVED_STATEMENT = [
    "theorem supp39 {V : Type u} {E : Type v} (G : UGraph V E) (_hG : G.IsSimple)",
    "    (hcut : ∃ e : E, G.IsCutEdge e) : ¬ G.Orientable := by",
]
APPROVED_LEMMA = [
    "theorem path_avoiding_of_dpath_to_tail (G : UGraph V E) (o : E → V × V)",
    "    (hdir : ∀ e : E, s((o e).1, (o e).2) = G.ends e) (e₀ : E) {a : V} (ha : (o e₀).1 = a)",
    "    {x : V} (p : (DGraph.mk o).Path x a) : Nonempty ((G.deleteEdge e₀).Path x a) := by",
]

Ends = dict[str, frozenset]          # UGraph.ends : E → Sym2 V
Orient = dict[str, tuple[int, int]]  # o : E → V × V
Steps = list[tuple[str, int, int]]   # a path: (edge, from, to) for each edge, in order


def _require(path: Path) -> list[str]:
    if not path.exists():
        sys.exit(f"error: cannot find {path}; run this script inside the GraphCh10 project")
    return path.read_text(encoding="utf-8").splitlines()


# ---------------------------------------------------------------------------
# 1. The definitions, mirroring GraphCh10/Definitions.lean
# ---------------------------------------------------------------------------

def edge_name(u: int, w: int) -> str:
    return f"{{{min(u, w)},{max(u, w)}}}"


def make_ends(pairs: list[tuple[int, int]]) -> Ends:
    """`G.ends e = s(u, w)` for each listed edge."""
    return {edge_name(u, w): frozenset((u, w)) for u, w in pairs}


def other_end(p: frozenset, u: int) -> int:
    """The other vertex of the set {u, w} (u itself for a loop)."""
    rest = [w for w in p if w != u]
    return rest[0] if rest else u


def upath(vs: list[int], ends: Ends, x: int, y: int) -> Steps | None:
    """A `UGraph.Path x y`, as its steps, found by breadth-first search; None if there is none.
    The empty list is `Path.nil x`; each step (e, u, w) is a `cons e h …` with ends e = s(u, w)."""
    parent: dict[int, tuple[str, int] | None] = {x: None}
    queue = deque([x])
    while queue:
        u = queue.popleft()
        if u == y:
            break
        for e, p in ends.items():
            if u in p:
                w = other_end(p, u)
                if w not in parent:
                    parent[w] = (e, u)
                    queue.append(w)
    if y not in parent:
        return None
    steps, v = [], y
    while parent[v] is not None:
        e, u = parent[v]
        steps.append((e, u, v))
        v = u
    return steps[::-1]


def is_upath(ends: Ends, steps: Steps, x: int, y: int) -> bool:
    """`steps` really is a `UGraph.Path x y` in the graph with these ends."""
    cur = x
    for e, u, w in steps:
        if e not in ends or u != cur or ends[e] != frozenset((u, w)):
            return False
        cur = w
    return cur == y


def connected(vs: list[int], ends: Ends) -> bool:
    """`Connected G := ∀ x y : V, Nonempty (G.Path x y)`."""
    return all(upath(vs, ends, x, y) is not None for x in vs for y in vs)


def delete_edge(ends: Ends, e0: str) -> Ends:
    """`G.deleteEdge e₀`: the edges `{e // e ≠ e₀}`, with the same ends (`G.ends e.1`)."""
    return {e: p for e, p in ends.items() if e != e0}


def is_cut_edge(vs: list[int], ends: Ends, e: str) -> bool:
    """`IsCutEdge G e := ¬ (G.deleteEdge e).Connected` (the literal "G − e is disconnected")."""
    return not connected(vs, delete_edge(ends, e))


def cut_edges(vs: list[int], ends: Ends) -> list[str]:
    return [e for e in ends if is_cut_edge(vs, ends, e)]


def components(vs: list[int], ends: Ends) -> list[list[int]]:
    """The connected components: classes of 'there is a path between them'."""
    comps: list[list[int]] = []
    for v in vs:
        if not any(v in c for c in comps):
            comps.append([w for w in vs if upath(vs, ends, v, w) is not None])
    return comps


def is_simple(ends: Ends) -> bool:
    """`UGraph.IsSimple := ¬ HasMultipleEdges ∧ ∀ e, ¬ IsLoop e`."""
    sets = list(ends.values())
    return len(set(sets)) == len(sets) and all(len(p) == 2 for p in sets)


def dpath(vs: list[int], o: Orient, x: int, y: int) -> Steps | None:
    """A `DGraph.Path x y` in `DGraph.mk o`: every step (e, u, w) has o[e] == (u, w)."""
    parent: dict[int, tuple[str, int] | None] = {x: None}
    queue = deque([x])
    while queue:
        u = queue.popleft()
        if u == y:
            break
        for e, (t, h) in o.items():
            if t == u and h not in parent:
                parent[h] = (e, u)
                queue.append(h)
    if y not in parent:
        return None
    steps, v = [], y
    while parent[v] is not None:
        e, u = parent[v]
        steps.append((e, u, v))
        v = u
    return steps[::-1]


def is_dpath(o: Orient, steps: Steps, x: int, y: int) -> bool:
    cur = x
    for e, u, w in steps:
        if u != cur or o[e] != (u, w):
            return False
        cur = w
    return cur == y


def strongly_connected(vs: list[int], o: Orient) -> bool:
    """`StronglyConnected := ∀ x y : V, Nonempty (G.Path x y)`."""
    return all(dpath(vs, o, x, y) is not None for x in vs for y in vs)


def failing_pairs(vs: list[int], o: Orient) -> list[tuple[int, int]]:
    """The pairs (x, y) with NO directed path from x to y."""
    return [(x, y) for x in vs for y in vs if dpath(vs, o, x, y) is None]


def directions_ok(ends: Ends, o: Orient) -> bool:
    """`∀ e, s((o e).1, (o e).2) = G.ends e`: each edge gets one of its two directions."""
    return set(o) == set(ends) and all(frozenset(o[e]) == ends[e] for e in ends)


def is_orientation(vs: list[int], ends: Ends, o: Orient) -> bool:
    """`IsOrientation G o := (∀ e, …) ∧ (DGraph.mk o).StronglyConnected`."""
    return directions_ok(ends, o) and strongly_connected(vs, o)


def all_direction_choices(ends: Ends):
    """Every o with `directions_ok`: 2^m of them for m non-loop edges."""
    names = list(ends)
    opts = [[tuple(sorted(ends[e])), tuple(sorted(ends[e], reverse=True))] for e in names]
    for choice in product(*opts):
        yield dict(zip(names, choice))


def orientable(vs: list[int], ends: Ends) -> bool:
    """`Orientable G := ∃ o, G.IsOrientation o` (by trying every choice of directions)."""
    return any(strongly_connected(vs, o) for o in all_direction_choices(ends))


def lemma_convert(o: Orient, e0: str, a: int, steps: Steps) -> tuple[Steps, list[tuple[str, str]]]:
    """`Supp39.path_avoiding_of_dpath_to_tail`, the same recursion as the Lean proof.

    Input: a directed path (steps) from x to a, where a = (o e₀).1. Output: an undirected path in
    G − e₀ from x to a, and a trace of the cases used: ("keep", e) for `e ≠ e₀` (put ⟨e, he⟩ in
    front of the converted rest), ("stop", e₀) for `e = e₀` (then x = a; return Path.nil), and
    ("nil", "") when the directed path has run out (Path.nil)."""
    assert o[e0][0] == a                                        # ha
    if not steps:                                               # | nil x
        return [], [("nil", "")]
    e, x, y = steps[0]                                          # | cons e h p
    assert o[e] == (x, y)                                       # hxy
    if e == e0:                                                 # by_cases he : e = e₀
        assert x == a                                           # hxa (calc), then subst
        return [], [("stop", e)]
    q, trace = lemma_convert(o, e0, a, steps[1:])               # obtain ⟨q⟩ := ih ha
    return [(e, x, y)] + q, [("keep", e)] + trace               # Path.cons ⟨e, he⟩ hends q


def path_via_e0(vs: list[int], o: Orient, e0: str, x: int) -> Steps | None:
    """A directed path x → a that USES e₀: x → a, then e₀ (a → b), then b → a. Lean paths may
    repeat vertices. Exists only when the head b has a directed path back to a."""
    a, b = o[e0]
    p1, p2 = dpath(vs, o, x, a), dpath(vs, o, b, a)
    if p1 is None or p2 is None:
        return None
    return p1 + [(e0, a, b)] + p2


# ---------------------------------------------------------------------------
# 2. The examples (positions are hand-chosen; every fact is computed)
# ---------------------------------------------------------------------------

EXAMPLES = [
    dict(name="Two triangles joined by one edge", short="two triangles",
         edges=[(0, 1), (1, 2), (2, 0), (3, 4), (4, 5), (5, 3), (2, 3)], e0=(2, 3), x=0,
         pos={0: (-2.7, 1.0), 1: (-2.7, -1.0), 2: (-1.0, 0.0), 3: (1.0, 0.0), 4: (2.7, 1.0),
              5: (2.7, -1.0)}),
    dict(name="A triangle with a tail (two cut edges)", short="triangle with a tail",
         edges=[(0, 1), (1, 2), (2, 0), (2, 3), (3, 4)], e0=(2, 3), x=0,
         pos={0: (-2.8, 1.0), 1: (-2.8, -1.0), 2: (-1.1, 0.0), 3: (0.7, 0.0), 4: (2.5, 0.0)}),
    dict(name="CONTRAST: a 6-cycle (no cut edge)", short="6-cycle (contrast)",
         edges=[(0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (5, 0)], e0=(0, 1), x=3,
         pos={0: (-2.4, 0.0), 1: (-1.2, 1.26), 2: (1.2, 1.26), 3: (2.4, 0.0), 4: (1.2, -1.26),
              5: (-1.2, -1.26)}),
]
for _ex in EXAMPLES:
    _ex["vs"] = sorted(_ex["pos"])
    _ex["ends"] = make_ends(_ex["edges"])
    # starting directions: each edge as listed, u → w
    _ex["orient"] = {edge_name(u, w): (u, w) for u, w in _ex["edges"]}


def small_simple_graphs(n: int):
    """Every simple graph on the vertices 0..n-1 (as ends dicts)."""
    pairs = list(combinations(range(n), 2))
    for bits in product((0, 1), repeat=len(pairs)):
        yield make_ends([p for p, b in zip(pairs, bits) if b])


# ---------------------------------------------------------------------------
# 3. Programmatic checks
# ---------------------------------------------------------------------------

def check_statement() -> None:
    """The Lean file still contains exactly the approved statements."""
    lines = _require(PROOF_FILE)
    i = next(i for i, ln in enumerate(lines) if ln.startswith("theorem supp39"))
    assert lines[i:i + 2] == APPROVED_STATEMENT, "the statement of supp39 has changed"
    j = next(j for j, ln in enumerate(lines) if ln.startswith("theorem path_avoiding"))
    assert lines[j:j + 3] == APPROVED_LEMMA, "the statement of the helper lemma has changed"


def check_lemma_everywhere(vs: list[int], ends: Ends, o: Orient) -> int:
    """For every e₀ and every x with a directed path to a = tail of e₀: the conversion of the
    shortest path (and of a path through e₀, when one exists) is a path x → a in G − e₀."""
    k = 0
    for e0 in ends:
        a = o[e0][0]
        minus = delete_edge(ends, e0)
        for x in vs:
            for p in (dpath(vs, o, x, a), path_via_e0(vs, o, e0, x)):
                if p is None:
                    continue
                assert is_dpath(o, p, x, a)
                q, _tr = lemma_convert(o, e0, a, p)
                assert is_upath(minus, q, x, a), (ends, o, e0, x)
                k += 1
    return k


def run_checks() -> dict:
    """Assert every fact the pictures and the walkthrough rely on. Returns summary numbers."""
    check_statement()
    stats: dict = dict(per_example=[])
    for ex in EXAMPLES:
        vs, ends = ex["vs"], ex["ends"]
        assert is_simple(ends) and connected(vs, ends)
        assert directions_ok(ends, ex["orient"])
        cuts = cut_edges(vs, ends)
        n_o = n_sc = 0
        for o in all_direction_choices(ends):
            n_o += 1
            sc = strongly_connected(vs, o)
            n_sc += sc
            if cuts:
                assert not sc  # the theorem, on this example
            check_lemma_everywhere(vs, ends, o)
            for e0 in cuts:  # the "far side" of e₀ never reaches its tail a
                a, b = o[e0]
                comps = components(vs, delete_edge(ends, e0))
                ca = next(c for c in comps if a in c)
                cb = next(c for c in comps if b in c)
                assert ca != cb
                for v in cb:
                    assert dpath(vs, o, v, a) is None
                    assert upath(vs, delete_edge(ends, e0), v, a) is None
        # cross-check with NetworkX: connected graph, so cut edges = bridges
        g = nx.Graph()
        g.add_nodes_from(vs)
        g.add_edges_from(ex["edges"])
        assert nx.is_connected(g)
        assert sorted(cuts) == sorted(edge_name(u, w) for u, w in nx.bridges(g))
        stats["per_example"].append(dict(name=ex["short"], m=len(ends), cuts=cuts, n_o=n_o,
                                         n_sc=n_sc))
    # Expected shapes of the three examples.
    assert stats["per_example"][0]["cuts"] == ["{2,3}"]
    assert stats["per_example"][1]["cuts"] == ["{2,3}", "{3,4}"]
    assert stats["per_example"][2]["cuts"] == [] and stats["per_example"][2]["n_sc"] == 2
    # The starting directions of the example: the left triangle reaches a = 2, the right does not.
    ex = EXAMPLES[0]
    o = ex["orient"]
    assert [v for v in ex["vs"] if dpath(ex["vs"], o, v, 2) is not None] == [0, 1, 2]

    # Every simple graph on 1..5 vertices: a cut edge ⇒ no choice of directions is strongly
    # connected; the helper lemma's conversion is checked on 1..4 vertices for every choice.
    n_graphs = n_cut = n_orient_checked = n_conv = 0
    for n in range(1, 6):
        vs = list(range(n))
        for ends in small_simple_graphs(n):
            n_graphs += 1
            is_conn = connected(vs, ends)
            cuts = cut_edges(vs, ends)
            if not is_conn and ends:  # literal definition: every edge of a disconnected graph
                assert cuts == list(ends)
            if cuts:
                n_cut += 1
            for o in all_direction_choices(ends):
                if cuts:
                    n_orient_checked += 1
                    assert not strongly_connected(vs, o), (n, ends, o)
                if n <= 4:
                    n_conv += check_lemma_everywhere(vs, ends, o)
            # NetworkX agrees on connectivity
            g = nx.Graph()
            g.add_nodes_from(vs)
            g.add_edges_from(tuple(p) for p in ends.values())
            assert nx.is_connected(g) == is_conn
    stats.update(n_graphs=n_graphs, n_cut=n_cut, n_orient_checked=n_orient_checked,
                 n_conv=n_conv)
    return stats


# ---------------------------------------------------------------------------
# 4. Shared drawing helpers
# ---------------------------------------------------------------------------

COLOR_VERTEX = "#3B6FB6"   # blue vertex fill
COLOR_EDGE = "#9A9A9A"     # an ordinary edge
COLOR_CUT = "#D1495B"      # red: the edge e₀
COLOR_PATH = "#2F80ED"     # bright blue: the directed path x → a
COLOR_KEEP = "#1E8C45"     # green: an edge kept by the lemma / the undirected path in G − e₀
COLOR_FOCUS = "#F2B705"    # gold: tags, the e = e₀ case
COLOR_NOREACH = "#C0392B"  # dark red ring: no directed path to a
COLOR_TEXT = "#222222"
COLOR_WARN = "#9A2A2A"
COLOR_OK = "#1E8C45"
COLOR_CODE_BG = "#FBFBF8"
COLOR_CODE_HL = "#FFF1B8"
COMP_COLORS = ["#3B6FB6", "#B5651D", "#7B3FB8", "#5E6B6B"]  # components of G − e₀

NODE_R = 0.27
XLIM, YLIM = (-3.4, 3.4), (-1.85, 1.95)


def frame(ax, xlim=XLIM, ylim=YLIM) -> None:
    ax.set_xlim(*xlim)
    ax.set_ylim(*ylim)
    ax.set_aspect("equal")
    ax.axis("off")


def _points_per_unit(ax) -> float:
    """How many typographic points one data unit is (aspect is equal)."""
    fig = ax.figure
    bb = ax.get_position()
    w_pt = bb.width * fig.get_figwidth() * 72
    h_pt = bb.height * fig.get_figheight() * 72
    x0, x1 = ax.get_xlim()
    y0, y1 = ax.get_ylim()
    return min(w_pt / (x1 - x0), h_pt / (y1 - y0))


def draw_graph(ax, pos, ends: Ends, o: Orient | None = None, styles: dict | None = None,
               removed: str | None = None, vfill: dict | None = None,
               rings: dict | None = None, tags: dict | None = None,
               elabels: dict | None = None, r: float = NODE_R, fs: float = 13,
               width: float = 2.4, tag_fs: float | None = None) -> None:
    """Draw edges (arrows if `o` is given) and vertices. Call `frame` first.

    styles: e -> dict(color, lw, ls, z, outline); removed: an edge drawn as a faint dotted line
    ('removed'); vfill / rings: per-vertex fill colour / dashed ring colour; tags: v -> text
    placed above the vertex; elabels: e -> (text, colour) placed beside the edge."""
    styles, vfill, rings = styles or {}, vfill or {}, rings or {}
    tags, elabels = tags or {}, elabels or {}
    ppu = _points_per_unit(ax)
    shrink = (r + 0.04) * ppu
    for e, p in ends.items():
        st = dict(color=COLOR_EDGE, lw=width, ls="-", z=2, outline=False)
        st.update(styles.get(e, {}))
        if o is not None and e != removed:
            u, w = o[e]
            arrow = "-|>"
        else:
            u, w = sorted(p)
            arrow = "-"
        if e == removed:
            st.update(color="#BBBBBB", lw=1.6, ls=(0, (2, 3)), z=1.5)
        patch = FancyArrowPatch(pos[u], pos[w], arrowstyle=arrow,
                                mutation_scale=max(12, 0.5 * ppu * 0.6), color=st["color"],
                                linewidth=st["lw"], linestyle=st["ls"], shrinkA=shrink,
                                shrinkB=shrink, zorder=st["z"])
        if st["outline"]:
            patch.set_path_effects([pe.withStroke(linewidth=st["lw"] + 4, foreground="#333333")])
        ax.add_patch(patch)
        if e in elabels:
            text, col = elabels[e]
            (x1, y1), (x2, y2) = pos[u], pos[w]
            mx, my = (x1 + x2) / 2, (y1 + y2) / 2
            dx, dy = x2 - x1, y2 - y1
            ln = (dx * dx + dy * dy) ** 0.5
            nx_, ny_ = -dy / ln, dx / ln
            if ny_ < 0 or (abs(ny_) < 1e-9 and nx_ < 0):
                nx_, ny_ = -nx_, -ny_
            ax.text(mx + 0.27 * nx_, my + 0.27 * ny_, text, ha="center", va="center",
                    fontsize=fs * 0.78, fontweight="bold", color=col, zorder=6,
                    bbox=dict(boxstyle="round,pad=0.15", fc="white", ec="none", alpha=0.9))
    for v, (x, y) in pos.items():
        if v in rings:
            ax.add_patch(Circle((x, y), r + 0.11, fill=False, edgecolor=rings[v], linewidth=2.4,
                                linestyle=(0, (3, 2)), zorder=3.5))
        ax.add_patch(Circle((x, y), r, facecolor=vfill.get(v, COLOR_VERTEX),
                            edgecolor="#22303F", linewidth=1.3, zorder=4))
        ax.text(x, y, str(v), ha="center", va="center", fontsize=fs, fontweight="bold",
                color="white", zorder=5)
        if v in tags:
            ax.text(x, y + r + 0.17, tags[v], ha="center", va="bottom", fontsize=tag_fs or fs * 0.7,
                    fontweight="bold", color="#5A4500", zorder=6,
                    bbox=dict(boxstyle="round,pad=0.15", fc="#FFF4C2", ec=COLOR_FOCUS))


def fmt_set(vs) -> str:
    return "{" + ", ".join(map(str, vs)) + "}" if vs else "∅ (none)"


def fmt_dpath(x: int, steps: Steps | None) -> str:
    if steps is None:
        return "none"
    return " → ".join([str(x)] + [str(w) for _e, _u, w in steps])


def fmt_upath(x: int, steps: Steps | None) -> str:
    if steps is None:
        return "none"
    return " – ".join([str(x)] + [str(w) for _e, _u, w in steps])


# ---------------------------------------------------------------------------
# 5. The facts about the current state (all computed)
# ---------------------------------------------------------------------------

def compute_facts(ex_def: dict, o: Orient, e0: str, x: int, mode: str) -> dict:
    vs, ends = ex_def["vs"], ex_def["ends"]
    a, b = o[e0]
    minus = delete_edge(ends, e0)
    comps = components(vs, minus)
    cuts = cut_edges(vs, ends)
    reach = [v for v in vs if dpath(vs, o, v, a) is not None]
    fails = failing_pairs(vs, o)
    fail = (b, a) if (b, a) in fails else (fails[0] if fails else None)
    via = path_via_e0(vs, o, e0, x)
    path = via if mode == "via" and via is not None else dpath(vs, o, x, a)
    conv, trace = lemma_convert(o, e0, a, path) if path is not None else (None, [])
    n_o = n_sc = 0
    for oo in all_direction_choices(ends):
        n_o += 1
        n_sc += strongly_connected(vs, oo)
    return dict(name=ex_def["name"], vs=vs, ends=ends, o=o, e0=e0, a=a, b=b, x=x, mode=mode,
                minus=minus, comps=comps, cuts=cuts, cut=e0 in cuts, hyp=bool(cuts),
                simple=is_simple(ends), conn=connected(vs, ends), dir_ok=directions_ok(ends, o),
                sc=not fails, fail=fail, reach=reach,
                noreach=[v for v in vs if v not in reach],
                via=via, via_used=mode == "via" and via is not None, path=path, conv=conv,
                trace=trace, n_o=n_o, n_sc=n_sc, m=len(ends),
                gpath=upath(vs, ends, x, a))


# ---------------------------------------------------------------------------
# 6. Static summary figure (visualizations/supp39.png)
# ---------------------------------------------------------------------------

GLOSSARY = [
    ("undirected graph", "vertices (dots) and edges (lines); each edge joins a set {u, w}"),
    ("path", "a sequence of edges walking from one vertex to another (length 0 allowed)"),
    ("connected", "there is a path between every two vertices"),
    ("G − e", "the graph G with the single edge e removed (all vertices stay)"),
    ("cut edge", "an edge e such that G − e is disconnected (not connected)"),
    ("directed graph", "every edge is an arrow, from its tail to its head"),
    ("tail / head", "the vertex an arrow starts at / points to"),
    ("directed path", "a path that follows every arrow from tail to head"),
    ("strongly connected", "a directed path from every vertex to every vertex"),
    ("orientation", "directions for all edges of a simple graph, making it strongly connected"),
    ("orientable", "at least one orientation exists"),
]


def build_figure(stats: dict) -> plt.Figure:
    fig = plt.figure(figsize=(19, 14.5), facecolor="white")
    gs = GridSpec(3, 3, figure=fig, height_ratios=[1.0, 1.0, 1.05], hspace=0.34, wspace=0.06,
                  left=0.025, right=0.975, top=0.855, bottom=0.025)
    fig.suptitle("Supplementary Exercise 39:  a graph with a cut edge is not orientable",
                 fontsize=20, fontweight="bold", color=COLOR_TEXT, y=0.985)
    fig.text(0.5, 0.955, "\"Show that a graph is not orientable if it has a cut edge.\"   "
             "Proved in Lean as GraphCh10.supp39 (by contradiction).", ha="center",
             fontsize=11.5, color="#444444")
    fig.text(0.5, 0.937, "Every picture shows a REAL choice of directions. The proof's "
             "'suppose an orientation exists' cannot be drawn: no orientation exists. "
             "Run  python visualizations/supp39.py  for the interactive walkthrough.",
             ha="center", fontsize=10.5, color=COLOR_WARN, style="italic")

    ex = EXAMPLES[0]
    e0 = edge_name(*ex["e0"])
    F = compute_facts(ex, ex["orient"], e0, ex["x"], "shortest")
    pos = ex["pos"]

    def head(ax, title, sub):
        ax.set_title(title, fontsize=13.5, fontweight="bold", pad=24)
        ax.text(0.5, 1.02, sub, transform=ax.transAxes, ha="center", va="bottom",
                fontsize=9.8, color="#444444")

    # (1) G and its cut edge
    ax = fig.add_subplot(gs[0, 0])
    frame(ax)
    draw_graph(ax, pos, ex["ends"], styles={e0: dict(color=COLOR_CUT, lw=4.5)},
               elabels={e0: ("e₀", COLOR_CUT)})
    head(ax, "1. G and its cut edge e₀ (red)",
         f"G is simple and connected; its only cut edge is {', '.join(F['cuts'])} (computed)")

    # (2) G − e₀
    ax = fig.add_subplot(gs[0, 1])
    frame(ax)
    vfill = {v: COMP_COLORS[i] for i, c in enumerate(F["comps"]) for v in c}
    draw_graph(ax, pos, ex["ends"], removed=e0, vfill=vfill,
               elabels={e0: ("removed", "#888888")})
    head(ax, f"2. G − e₀ has {len(F['comps'])} components",
         " and ".join(fmt_set(c) for c in F["comps"]) + ": no path between them, so G − e₀ is "
         "disconnected")

    # (3) one attempt
    ax = fig.add_subplot(gs[0, 2])
    frame(ax)
    st = {e0: dict(color=COLOR_CUT, lw=4.5)}
    draw_graph(ax, pos, ex["ends"], o=F["o"], styles=st, rings={v: COLOR_NOREACH
                                                                for v in F["noreach"]},
               tags={F["a"]: "a (tail)", F["b"]: "b (head)"}, elabels={e0: ("e₀", COLOR_CUT)})
    head(ax, "3. One attempt at directions: NOT strongly connected",
         f"directed path to a = {F['a']} from {fmt_set(F['reach'])} only; red rings "
         f"{fmt_set(F['noreach'])} cannot reach a")

    # (4) the key lemma on a real path
    ax = fig.add_subplot(gs[1, 0])
    frame(ax)
    st = {e: dict(color=COLOR_KEEP, lw=5) for e, _u, _w in F["conv"]}
    st[e0] = dict(color=COLOR_CUT, lw=4.5)
    draw_graph(ax, pos, ex["ends"], o=F["o"], styles=st,
               tags={F["x"]: "x", F["a"]: "a"}, elabels={e0: ("e₀", COLOR_CUT)})
    head(ax, "4. Key step (helper lemma) on a real path",
         f"directed {fmt_dpath(F['x'], F['path'])} → undirected {fmt_upath(F['x'], F['conv'])} "
         "in G − e₀ (green)")

    # (5) contrast
    cx = EXAMPLES[2]
    ce0 = edge_name(*cx["e0"])
    CF = compute_facts(cx, cx["orient"], ce0, cx["x"], "via")
    ax = fig.add_subplot(gs[1, 1])
    frame(ax)
    draw_graph(ax, cx["pos"], cx["ends"], o=CF["o"],
               styles={e: dict(color=COLOR_PATH, lw=3) for e in cx["ends"]})
    head(ax, "5. Contrast: a 6-cycle has NO cut edge",
         f"arrows around the cycle: strongly connected {'✓' if CF['sc'] else '✗'}; "
         f"{CF['n_sc']} of {CF['n_o']} direction choices work (computed)")

    # (6) table of exhaustive checks
    ax = fig.add_subplot(gs[1, 2])
    ax.axis("off")
    rows = [[d["name"], str(d["m"]), ", ".join(d["cuts"]) or "none", f"{d['n_o']}",
             f"{d['n_sc']}"] for d in stats["per_example"]]
    rows.append([f"all {stats['n_graphs']:,} simple graphs" "\n(1 to 5 vertices)", "",
                 f"{stats['n_cut']:,} have one",
                 f"{stats['n_orient_checked']:,}", "0"])
    table = ax.table(cellText=rows, colLabels=["graph", "edges", "cut edges", "direction\nchoices",
                                               "strongly\nconnected"],
                     loc="center", cellLoc="center", colWidths=[0.36, 0.09, 0.2, 0.15, 0.15])
    table.auto_set_font_size(False)
    table.set_fontsize(10)
    table.scale(1, 2.5)
    for (rr, cc), cell in table.get_celld().items():
        cell.set_edgecolor("#CCCCCC")
        if rr == 0:
            cell.set_facecolor("#EFEFEF")
            cell.set_text_props(fontweight="bold")
        elif cc == 4:
            ok = rows[rr - 1][4] == "0"
            cell.set_text_props(color=COLOR_WARN if ok else COLOR_OK, fontweight="bold")
    head(ax, "6. Every choice of directions, tried (computed)",
         "with a cut edge: 0 strongly connected choices; last row counts graphs WITH a cut edge")

    # (7) glossary and proof outline
    ax = fig.add_subplot(gs[2, :])
    ax.axis("off")
    ax.add_patch(plt.Rectangle((0, 0), 1, 1, transform=ax.transAxes, facecolor="#F7F7F7",
                               edgecolor="#D0D0D0"))
    ax.text(0.012, 0.95, "Glossary (plain English)", transform=ax.transAxes, fontsize=12.5,
            fontweight="bold", va="top")
    for i, (term, mean) in enumerate(GLOSSARY):
        y = 0.83 - i * 0.073
        ax.text(0.012, y, term, transform=ax.transAxes, fontsize=10.2, fontweight="bold",
                va="top", color=COLOR_VERTEX)
        ax.text(0.115, y, mean, transform=ax.transAxes, fontsize=10.2, va="top")
    proof = [
        "Paper proof = Lean proof (GraphCh10/Exercises/Supp39.lean)",
        "",
        "obtain ⟨e₀, he₀⟩ := hcut          take a cut edge e₀",
        "rintro ⟨o, hdir, hstrong⟩         SUPPOSE o is an orientation (goal: False)",
        "set a := (o e₀).1                 a = the tail of e₀",
        "have hreach                       every x: directed path x → a (hstrong),",
        "                                    so an undirected path x → a in G − e₀ (lemma)",
        "have hconn                        so G − e₀ is connected",
        "exact he₀ hconn                   but e₀ is a cut edge: contradiction  ∎",
        "",
        "Lemma path_avoiding_of_dpath_to_tail (induction on the directed path):",
        "  keep every edge e ≠ e₀; on reaching e₀ we are at its tail a: stop.",
        "_hG (G simple) is in the approved statement but the proof never uses it.",
    ]
    ax.text(0.47, 0.95, proof[0], transform=ax.transAxes, fontsize=12.5, fontweight="bold",
            va="top")
    ax.text(0.47, 0.86, "\n".join(proof[2:]), transform=ax.transAxes, fontsize=9.8, va="top",
            family="DejaVu Sans Mono", linespacing=1.5)

    legend = [
        Patch(facecolor=COLOR_VERTEX, edgecolor="#22303F", label="vertex"),
        Line2D([], [], color=COLOR_CUT, linewidth=4, label="the cut edge e₀"),
        Line2D([], [], color=COLOR_EDGE, linewidth=3, label="other edge"),
        Line2D([], [], color=COLOR_KEEP, linewidth=4, label="undirected path avoiding e₀"),
        Line2D([], [], color=COLOR_NOREACH, linewidth=2.4, linestyle="--",
               label="ring: no directed path to a"),
        Patch(facecolor=COMP_COLORS[1], label="second component of G − e₀"),
    ]
    fig.legend(handles=legend, loc="upper center", ncol=6, frameon=False, fontsize=10.5,
               bbox_to_anchor=(0.5, 0.928))
    return fig


# ---------------------------------------------------------------------------
# 7. Lean source, read from the project (the source of truth)
# ---------------------------------------------------------------------------

def _block(lines: list[str], start: str, end: str) -> list[str]:
    """The lines from the unique line starting with `start` to the first later line
    containing `end` (inclusive)."""
    hits = [i for i, ln in enumerate(lines) if ln.strip().startswith(start)]
    assert len(hits) == 1, f"expected exactly one line starting with {start!r}"
    j = next(j for j in range(hits[0], len(lines)) if end in lines[j])
    return [ln.rstrip() for ln in lines[hits[0]:j + 1]]


def _decl(lines: list[str], start: str) -> list[str]:
    """A declaration without its docstrings: from the unique line starting with `start` up to
    the next blank line, skipping one-line `/-- … -/` comments."""
    hits = [i for i, ln in enumerate(lines) if ln.strip().startswith(start)]
    assert len(hits) == 1, f"expected exactly one line starting with {start!r}"
    out = []
    for ln in lines[hits[0]:]:
        if not ln.strip():
            break
        if ln.strip().startswith("/--"):
            assert ln.strip().endswith("-/"), f"multi-line docstring inside {start!r}"
            continue
        out.append(ln.rstrip())
    return out


def read_lean_sources() -> dict[str, list[str]]:
    proof = _require(PROOF_FILE)
    lemmas = _require(LEMMAS_FILE)
    defs = _require(DEFS_FILE)
    return {
        "header": _block(proof, "Paper proof.", "Hence G has no orientation"),
        "defs_u": ["-- GraphCh10/Definitions.lean (excerpt; docstrings omitted)",
                   *_decl(defs, "structure UGraph"), "",
                   *_decl(defs, "inductive Path (G : UGraph V E)"), "",
                   *_decl(defs, "def Connected"), "",
                   *_decl(defs, "def deleteEdge"), "",
                   *_decl(defs, "def IsCutEdge")],
        "defs_d": ["-- GraphCh10/Definitions.lean (excerpt; docstrings omitted)",
                   *_decl(defs, "structure DGraph"), "",
                   *_decl(defs, "inductive Path (G : DGraph V E)"), "",
                   *_decl(defs, "def StronglyConnected"), "",
                   *_decl(defs, "def IsOrientation"), "",
                   *_decl(defs, "def Orientable")],
        "lemma": _block(proof, "theorem path_avoiding_of_dpath_to_tail",
                        "exact ⟨UGraph.Path.cons ⟨e, he⟩ hends q⟩"),
        "main": _block(proof, "theorem supp39", "exact he₀ hconn"),
        "lemmas": ["-- GraphCh10/Lemmas.lean (excerpt; namespace UGraph, G : UGraph V E)", "",
                   *_block(lemmas, "theorem path_trans", "Nonempty (G.Path x z) := by"),
                   "  ...  (proved by induction on p)", "",
                   *_block(lemmas, "theorem path_symm", "theorem path_symm"),
                   "  ...  (proved by induction on p)", "",
                   *_block(lemmas, "theorem connected_of_forall_path_to",
                           "exact G.path_trans p hcy")],
    }


SOURCE_NAMES = {
    "header": "Supp39.lean  ·  the paper proof (file comment)",
    "defs_u": "GraphCh10/Definitions.lean  ·  undirected notions",
    "defs_d": "GraphCh10/Definitions.lean  ·  directed notions, orientations",
    "lemma": "Supp39.lean  ·  helper lemma path_avoiding_of_dpath_to_tail",
    "main": "Supp39.lean  ·  the main theorem supp39",
    "lemmas": "GraphCh10/Lemmas.lean  ·  shared lemmas",
}


# ---------------------------------------------------------------------------
# 8. The walkthrough
# ---------------------------------------------------------------------------
# Each step: part, title, code source, `anchors` (substrings matching exactly one line) and
# `ranges` ((first, last): `first` matches exactly one line; the highlight runs to the first
# later line containing `last`), a focus kind, and three explanations: `math` (graph theory),
# `screen` (what the picture shows, computed from the current state), `lean` (Lean syntax).

P1, P2, P3, P4, P5 = ("Part 1 · What the theorem says", "Part 2 · The idea of the proof",
                      "Part 3 · Lean: the helper lemma", "Part 4 · Lean: the main theorem",
                      "Part 5 · Contrast and checks")


def _sc_sentence(F) -> str:
    if F["sc"]:
        return "These arrows ARE strongly connected ✓ (every vertex reaches every vertex)."
    u, w = F["fail"]
    return f"These arrows are NOT strongly connected: there is no directed path from {u} to {w}."


def _e0_sentence(F) -> str:
    return f"e₀ = {F['e0']} points from a = {F['a']} (tail) to b = {F['b']} (head)."


def _walk_sentence(ex, F) -> str:
    x, a = F["x"], F["a"]
    if F["path"] is None:
        return (f"Vertex x = {x} has NO directed path to a = {a} with these arrows, so there is "
                f"nothing to convert. Click a vertex in {fmt_set(F['reach'])} (those that do).")
    kind = ("a path through e₀; Lean paths may repeat vertices and edges" if F["via_used"]
            else "the shortest directed path")
    s = f"Directed path x → a ({kind}): {fmt_dpath(x, F['path'])}. "
    k = ex.walk_k(F)
    tr = F["trace"]
    if k < len(tr):
        s += (f"Walked {k} of {len(tr)} case(s) so far: one per edge read, plus a final 'nil' "
              "or 'e = e₀' case ('Walk the path ▶' continues). ")
    kept = [e for c, e in tr[:k] if c == "keep"]
    if kept:
        s += f"Kept: {', '.join(kept)}. "
    if any(c == "stop" for c, _e in tr[:k]):
        s += (f"Reached e₀ while standing at its tail a = {a}: stop (the rest is dropped; "
              "grey dashed where not hidden under kept edges). ")
    if k == len(tr):
        s += (f"Result: undirected path {fmt_upath(x, F['conv'])} from {x} to {a} in G − e₀ "
              "(green, bottom-left).")
        if not F["via_used"] and F["via"] is None:
            s += " This path never uses e₀."
    return s


def _via_note(F) -> str:
    if F["via_used"]:
        return ""
    if F["via"] is not None:
        return " Press 'Path: via e₀' to see a path that does use e₀."
    return (f" No directed path from x to a can use e₀ with these arrows: after crossing e₀ to "
            f"b = {F['b']} there is no directed way back to a = {F['a']}.")


def _hyp_warning(F) -> str:
    if F["hyp"]:
        return ""
    return ("⚠ CONTRAST GRAPH: it has no cut edge, so the theorem does not apply to it, and here "
            f"an orientation exists ({F['n_sc']} of {F['n_o']} choices work). e₀ is just a chosen "
            "edge; the helper lemma still works for it. ")


STEPS: list[dict] = [
    dict(
        part=P1, title="What the exercise says", code="main", focus="plain",
        ranges=[("theorem supp39", "¬ G.Orientable := by")],
        math=("An undirected graph has vertices (circles) and edges (lines); each edge joins a "
              "set {u, w} of vertices. A cut edge is an edge whose removal disconnects the graph. "
              "To orient a graph is to give every edge a direction so that you can get from any "
              "vertex to any other by following arrows. The theorem: if G has a cut edge, no "
              "such choice of directions exists, i.e. G is not orientable."),
        screen=lambda ex, F: (
            f"{F['name']}. The red edge e₀ = {F['e0']} is "
            + ("a cut edge (computed). " if F["cut"] else "NOT a cut edge (computed). ")
            + "The arrows are one real attempt at directing the edges; click any edge to "
              "reverse it, and see on the right that the attempt is never strongly connected."
            + (" " + _hyp_warning(F) if not F["hyp"] else "")),
        lean=("`theorem supp39 … := by` names the result. `G : UGraph V E` is an undirected "
              "graph with vertices of type V and edges of type E. The named inputs are "
              "hypotheses: `_hG : G.IsSimple` (G is simple) and `hcut : ∃ e : E, G.IsCutEdge e` "
              "('there exists an edge e that is a cut edge'). After the last colon comes the "
              "conclusion `¬ G.Orientable` ('G is not orientable'). `:= by` starts the proof, a "
              "list of tactics (commands)."),
    ),
    dict(
        part=P1, title="Paths and connected graphs", code="defs_u", focus="upath",
        anchors=["inductive Path (G : UGraph V E)", "| nil (x : V) : Path G x x",
                 "(h : G.ends e = s(x, y))", "def Connected"],
        math=("A path from u to v is a sequence of edges leading from u to v, each edge joining "
              "two consecutive vertices. A path with no edges (length 0) goes from a vertex to "
              "itself. In an undirected graph an edge can be used in either direction. A graph "
              "is connected if there is a path between every two vertices."),
        screen=lambda ex, F: (
            f"Green: an undirected path in G from x = {F['x']} to a = {F['a']}: "
            f"{fmt_upath(F['x'], F['gpath'])} ({len(F['gpath'])} edge(s); found by search, "
            f"arrow directions ignored). G is {'connected ✓' if F['conn'] else 'NOT connected'} "
            "(computed: a path between every pair). Click a vertex to move x."),
        lean=("`inductive Path` says a path is built in one of two ways: `Path.nil x`, the empty "
              "path at x, or `Path.cons e h p`, the edge e followed by a path p from y to z, "
              "where `h : G.ends e = s(x, y)` proves that e joins x and y. `s(x, y)` is the "
              "unordered pair {x, y}, so s(x, y) = s(y, x). `Nonempty (G.Path x y)` means "
              "'at least one path from x to y exists'. `Connected` asks this for all x y (∀)."),
    ),
    dict(
        part=P1, title="G − e₀ and cut edges", code="defs_u", focus="cut",
        anchors=["def deleteEdge", "⟨fun e => G.ends e.1⟩", "def IsCutEdge"],
        math=("G − e is G with the one edge e removed; all vertices stay. A cut edge is an edge "
              "e such that G − e is disconnected (not connected). This project uses the book's "
              "literal wording: in a graph that is already disconnected, every edge counts as a "
              "cut edge (the usual 'bridge' notion differs there). All examples here are "
              "connected, and then the two readings agree."),
        screen=lambda ex, F: (
            f"Bottom-left: G − e₀ for e₀ = {F['e0']}. It has {len(F['comps'])} component(s): "
            + " and ".join(fmt_set(c) for c in F["comps"]) + " (computed, coloured). "
            + (f"So e₀ is a cut edge ✓. Cut edges of this graph: {', '.join(F['cuts'])} "
               "('Next e₀' cycles through them)." if F["cut"] else
               "So e₀ is NOT a cut edge; this graph has no cut edge at all.")),
        lean=("`deleteEdge G e₀` has edge type `{e : E // e ≠ e₀}`: an edge e of G together "
              "with a proof that e ≠ e₀ (a 'subtype'). Such an edge is written `⟨e, he⟩`, "
              "where `he : e ≠ e₀`. `⟨fun e => G.ends e.1⟩` keeps the old endpoints; `e.1` is "
              "the underlying edge of G. `IsCutEdge G e` is defined as "
              "`¬ (G.deleteEdge e).Connected`; `¬` means 'not'."),
    ),
    dict(
        part=P1, title="Directed paths and strong connectivity", code="defs_d", focus="dpath",
        anchors=["structure DGraph", "ends : E → V × V", "inductive Path (G : DGraph V E)",
                 "(h : G.ends e = (x, y))", "def StronglyConnected"],
        math=("In a directed graph every edge is an arrow: it starts at its tail (initial "
              "vertex) and points to its head (terminal vertex). A directed path must follow "
              "every arrow from tail to head. A directed graph is strongly connected if there "
              "is a directed path from every vertex to every vertex (for each pair, both ways)."),
        screen=lambda ex, F: (
            (f"Blue: a directed path from x = {F['x']} to a = {F['a']}: "
             f"{fmt_dpath(F['x'], F['path'])}. " if F["path"] is not None else
             f"There is NO directed path from x = {F['x']} to a = {F['a']} (computed). ")
            + _sc_sentence(F)),
        lean=("A `DGraph V E` gives each edge an ordered pair `ends e : V × V` = (tail, head). "
              "Its `Path` is built like the undirected one, but `cons` needs "
              "`G.ends e = (x, y)`: the arrow must point from x to y. `StronglyConnected` says "
              "`∀ x y, Nonempty (G.Path x y)`."),
    ),
    dict(
        part=P1, title="Orientations: what 'orientable' means", code="defs_d", focus="reach",
        anchors=["def IsOrientation", "(∀ e : E, s((o e).1, (o e).2) = G.ends e) ∧",
                 "def Orientable"],
        math=("An orientation of a simple undirected graph is a choice of direction for every "
              "edge such that the resulting directed graph is strongly connected. A graph is "
              "orientable if at least one orientation exists. With m edges there are 2^m "
              "choices of directions; 'orientable' asks whether one of them is strongly "
              "connected."),
        screen=lambda ex, F: (
            f"This graph has m = {F['m']} edges: 2^{F['m']} = {F['n_o']} choices. The script "
            f"tried all of them: {F['n_sc']} are strongly connected (computed). "
            + _sc_sentence(F)
            + (" Red rings: vertices with no directed path to a." if F["noreach"] else "")),
        lean=("`o : E → V × V` gives each edge an ordered pair. `IsOrientation G o` has two "
              "parts joined by `∧` ('and'): first, for every e, the set {(o e).1, (o e).2} is "
              "G.ends e, so o only picks one of e's two directions (`.1` = tail, `.2` = head); "
              "second, `DGraph.mk o` (the directed graph whose ends are o) is strongly "
              "connected. `Orientable G` is `∃ o, G.IsOrientation o`."),
    ),
    dict(
        part=P2, title="Proof by contradiction: SUPPOSE an orientation exists", code="header",
        focus="reach", ranges=[("Paper proof.", "some vertex b.")],
        math=("Take a cut edge e₀ and SUPPOSE some orientation o exists. It directs e₀ from a "
              "vertex a (the tail) to a vertex b (the head). Being strongly connected, it would "
              "give EVERY vertex x a directed path to a. We will show this forces G − e₀ to be "
              "connected. That is impossible, since e₀ is a cut edge. So the supposition is "
              "false: no orientation exists."),
        screen=lambda ex, F: (
            _hyp_warning(F)
            + "The 'suppose' world cannot be drawn: it does not exist. The arrows here are one "
              "REAL attempt. " + _e0_sentence(F) + " ('Flip e₀' swaps a and b.) "
            + _sc_sentence(F)),
        lean=("To prove `¬ P` in Lean is to prove 'P leads to False'. Here P is "
              "`G.Orientable`, so the Lean proof assumes an orientation and derives `False`, "
              "a contradiction."),
    ),
    dict(
        part=P2, title="Key step: a directed path to a gives a path avoiding e₀", code="header",
        focus="convert", ranges=[("**Key step.**", "given by the induction hypothesis")],
        math=("Take a directed path from x to a and read its edges in order. Each arrow is also "
              "an edge of G, so keep it, unless it is e₀. If we reach e₀, we are standing at its "
              "tail, which is a: we are already done, so stop. What we kept is an undirected "
              "path from x to a that never uses e₀, i.e. a path in G − e₀. This step needs no "
              "'suppose': it works for ANY choice of directions, so we can run it on screen."),
        screen=lambda ex, F: _walk_sentence(ex, F) + _via_note(F),
        lean=("This is the helper lemma `path_avoiding_of_dpath_to_tail` (Part 3), proved by "
              "induction on the directed path."),
    ),
    dict(
        part=P2, title="Where it breaks: the far side cannot reach a", code="header",
        focus="reach", ranges=[("**Conclusion.**", "Hence G has no orientation")],
        math=("If every x had a directed path to a, the key step would join every x to a in "
              "G − e₀, so G − e₀ would be connected. But it is not: vertices on b's side have "
              "no path to a in G − e₀ at all. So they cannot have DIRECTED paths to a either "
              "(the only edge back across is e₀, and it points away from a). Strong "
              "connectivity fails — for every choice of directions."),
        screen=lambda ex, F: (
            _hyp_warning(F)
            + f"Directed path to a = {F['a']} from: {fmt_set(F['reach'])}; their converted "
              f"paths (green, bottom-left) stay inside a's part of G − e₀. No directed path to "
              f"a from: {fmt_set(F['noreach'])} (red rings). "
            + (f"These are b's side of G − e₀ ({fmt_set(next(c for c in F['comps'] if F['b'] in c))})."
               if F["cut"] else "")
            + " Flip edges: while e₀ is a cut edge, the red set is never empty."),
        lean=("In Lean this is the main theorem (Part 4): `hreach`, then `hconn`, then "
              "`exact he₀ hconn`."),
    ),
    dict(
        part=P3, title="The lemma's statement", code="lemma", focus="convert",
        ranges=[("theorem path_avoiding_of_dpath_to_tail", "{x : V} (p : (DGraph.mk o).Path x a)")],
        math=("Let o direct every edge of G, and let a be the tail of e₀. Then every directed "
              "path from x to a gives an undirected path from x to a in G − e₀. The lemma does "
              "NOT assume strong connectivity or that e₀ is a cut edge."),
        screen=lambda ex, F: _walk_sentence(ex, F),
        lean=("Inputs: `o : E → V × V` (the directions); `hdir`: each o e is a direction of e; "
              "`e₀ : E`; `ha : (o e₀).1 = a` (a is the tail of e₀); `p`, a directed path from x "
              "to a in `DGraph.mk o`. Braces `{a : V}` mark inputs Lean infers by itself. The "
              "conclusion `Nonempty ((G.deleteEdge e₀).Path x a)`: some path from x to a in "
              "G − e₀ exists. `Nonempty T` says T has an element; `⟨q⟩` packs a path q into it."),
    ),
    dict(
        part=P3, title="induction p — case nil: the empty path", code="lemma", focus="convert",
        ranges=[("induction p with", "exact ⟨UGraph.Path.nil x⟩")],
        math=("Induction on the path: prove the claim for the empty path, and show that if it "
              "holds for the rest of a path, it holds for the whole path. Empty case: the "
              "directed path has no edges, so x = a, and the empty undirected path works."),
        screen=lambda ex, F: (
            f"Here x = a = {F['a']}: the directed path is empty, and so is the result."
            if F["x"] == F["a"] else
            f"Here x = {F['x']} ≠ a = {F['a']}. Click vertex a = {F['a']} to see this case. "
            "(The recursion also ends in this case once the whole path has been read.)"),
        lean=("`induction p with` splits the proof into one case per way a path is built: "
              "`nil` and `cons`. In case `| nil x =>` the goal is a path from x to x in G − e₀; "
              "`exact ⟨UGraph.Path.nil x⟩` supplies the empty one. `exact t` finishes the goal "
              "with the term t."),
    ),
    dict(
        part=P3, title="case cons: look at the first edge", code="lemma", focus="first",
        ranges=[("| @cons x y z e h p ih =>", "by_cases he : e = e₀")],
        math=("Otherwise the path starts with an arrow e from x to some vertex y and continues "
              "with a directed path from y to a. The induction hypothesis says the claim already "
              "holds for that shorter rest. Two cases: e is e₀, or it is not."),
        screen=lambda ex, F: (
            "No directed path from x to a here: " + _walk_sentence(ex, F)
            if F["path"] is None else
            (f"x = a: the path is empty (case nil). Click another vertex." if not F["path"] else
             f"Gold: the first edge {F['path'][0][0]}, directed {F['path'][0][1]} → "
             f"{F['path'][0][2]}; it {'IS' if F['path'][0][0] == F['e0'] else 'is not'} e₀.")),
        lean=("`| @cons x y z e h p ih =>` names the parts: the first edge `e`, the proof `h` "
              "that it points from x to y, the rest `p` (from y to z; here z is a) and `ih`, "
              "the induction hypothesis for p. `@` lets us name the implicit x y z. "
              "`have hxy : o e = (x, y) := h` records h in a clearer form (`have name : fact := "
              "proof`). `by_cases he : e = e₀` splits into `he : e = e₀` and `he : ¬ e = e₀`."),
    ),
    dict(
        part=P3, title="Case e = e₀: then x is a, so stop", code="lemma", focus="convert",
        ranges=[("· -- the first edge is e₀ itself", "exact ⟨UGraph.Path.nil x⟩")],
        math=("If the first edge is e₀, then x is its tail: x = (o e₀).1 = a. We are already "
              "at a, so the empty undirected path works; the rest of the directed path is "
              "dropped."),
        screen=lambda ex, F: (
            (_walk_sentence(ex, F) if F["via_used"] else
             "This case never happens for a shortest path." + _via_note(F))
            + (" When e₀ is a cut edge, a directed path to a never uses e₀ (there is no way back "
               "from b), but Lean must still handle the case: see it on the 6-cycle ('Next "
               "graph') with 'Path: via e₀'." if F["cut"] and not F["via_used"] else "")),
        lean=("`calc` proves `x = z` by a chain: x = (o e).1 (by `rw [hxy]`, i.e. rewrite using "
              "hxy), = (o e₀).1 (by `rw [he]`), = z (this is `ha`). `subst hxa` then replaces "
              "z by x everywhere, so the goal becomes a path from x to x, given by "
              "`⟨UGraph.Path.nil x⟩`."),
    ),
    dict(
        part=P3, title="Case e ≠ e₀: the edge survives in G − e₀", code="lemma", focus="first",
        ranges=[("· -- the first edge is not e₀", "_ = s(x, y) := by rw [hxy]")],
        math=("If e is not e₀, then e is still an edge of G − e₀, with the same endpoints "
              "{x, y}: removing e₀ does not touch e. As an undirected edge it simply joins x "
              "and y; its direction is forgotten."),
        screen=lambda ex, F: _walk_sentence(ex, F),
        lean=("`⟨e, he⟩` is e viewed as an edge of G − e₀: the edge e paired with the proof "
              "`he : e ≠ e₀`. `hends` says its ends in G − e₀ are s(x, y), by `calc`: they are "
              "G.ends e by definition (`rfl`: 'true by unfolding definitions'); G.ends e = "
              "s((o e).1, (o e).2) by `hdir e` read backwards (`.symm`); that is s(x, y) by "
              "`rw [hxy]`."),
    ),
    dict(
        part=P3, title="Use the induction hypothesis, put e in front", code="lemma",
        focus="convert",
        ranges=[("-- the rest of the path, from `y` to `a`",
                 "exact ⟨UGraph.Path.cons ⟨e, he⟩ hends q⟩")],
        math=("The rest of the directed path goes from y to a and is shorter, so by the "
              "induction hypothesis it becomes an undirected path q from y to a avoiding e₀. "
              "Putting e in front of q gives an undirected path from x to a avoiding e₀."),
        screen=lambda ex, F: _walk_sentence(ex, F),
        lean=("`ih ha` applies the induction hypothesis (it needs `ha` again) and gives "
              "`Nonempty (… .Path y a)`. `obtain ⟨q⟩ := …` unpacks it and names the path q. "
              "`UGraph.Path.cons ⟨e, he⟩ hends q` is 'the edge ⟨e, he⟩, then q', and the outer "
              "`⟨…⟩` packs it into `Nonempty`. The lemma is proved."),
    ),
    dict(
        part=P4, title="The statement: ¬ means 'leads to False'", code="main", focus="plain",
        ranges=[("theorem supp39", "¬ G.Orientable := by")],
        math=("Hypotheses: G is simple (no loops, no multiple edges) and has a cut edge. "
              "Conclusion: G is not orientable. Simplicity is assumed because the book defines "
              "orientations only for simple graphs; the argument itself never uses it."),
        screen=lambda ex, F: (
            f"This graph: simple {'✓' if F['simple'] else '✗'} (computed); cut edges: "
            f"{', '.join(F['cuts']) or 'none — the hypothesis hcut FAILS here'}."),
        lean=("`¬ G.Orientable` is by definition `G.Orientable → False`: to prove it, assume "
              "`G.Orientable` and derive `False`. The underscore in `_hG` tells Lean (and the "
              "reader) that the proof never uses this hypothesis; it stays because it is part "
              "of the approved statement."),
    ),
    dict(
        part=P4, title="Take a cut edge e₀; SUPPOSE an orientation o", code="main",
        focus="reach", ranges=[("-- take a cut edge e₀", "rintro ⟨o, hdir, hstrong⟩")],
        math=("Let e₀ be a cut edge. Suppose, for contradiction, that o is an orientation of G: "
              "every edge gets a direction (hdir), and the result is strongly connected "
              "(hstrong)."),
        screen=lambda ex, F: (
            _hyp_warning(F)
            + f"e₀ = {F['e0']}. The arrows on the left are a real attempt, not the supposed "
              "o: " + _sc_sentence(F)),
        lean=("`obtain ⟨e₀, he₀⟩ := hcut` unpacks the 'there exists': it names the cut edge e₀ "
              "and the fact `he₀ : G.IsCutEdge e₀`. Since the goal `¬ G.Orientable` means "
              "`G.Orientable → False`, `rintro ⟨o, hdir, hstrong⟩` assumes `G.Orientable` and "
              "unpacks it at once: o, `hdir : ∀ e, s((o e).1, (o e).2) = G.ends e` and "
              "`hstrong : (DGraph.mk o).StronglyConnected`. The goal is now `False`."),
    ),
    dict(
        part=P4, title="set a := the tail of e₀", code="main", focus="plain",
        ranges=[("-- let `a` be the tail of e₀", "set a : V := (o e₀).1")],
        math="Give the tail of e₀ a name: a. (Its head is b.)",
        screen=lambda ex, F: _e0_sentence(F) + " Press 'Flip e₀' to swap them: then a = "
                                               f"{F['b']}.",
        lean=("`set a : V := (o e₀).1` introduces the name a for `(o e₀).1` and replaces that "
              "expression by a everywhere. `.1` is the first entry of the ordered pair, i.e. "
              "the tail."),
    ),
    dict(
        part=P4, title="hreach: every x reaches a in G − e₀ (in the 'suppose' world)",
        code="main", focus="reach",
        ranges=[("-- every vertex `x` has a directed path",
                 "exact path_avoiding_of_dpath_to_tail G o hdir e₀ rfl p")],
        math=("For any vertex x, strong connectivity gives a directed path from x to a, and the "
              "helper lemma turns it into an undirected path from x to a in G − e₀."),
        screen=lambda ex, F: (
            _hyp_warning(F)
            + f"On the screen (a real attempt): the lemma works for every x that HAS a directed "
              f"path to a: {fmt_set(F['reach'])} (green paths, bottom-left). "
            + (f"For {fmt_set(F['noreach'])} there is none: `hstrong x a` is exactly what fails "
               "here. The supposed o would need it for every x." if F["noreach"] else
               "Here every x has one, because these arrows are strongly connected.")),
        lean=("`intro x` fixes an arbitrary vertex x. `obtain ⟨p⟩ := hstrong x a` takes a "
              "directed path p from x to a. `exact path_avoiding_of_dpath_to_tail G o hdir e₀ "
              "rfl p` applies the lemma; `rfl` proves `(o e₀).1 = a`, true by the definition of "
              "a."),
    ),
    dict(
        part=P4, title="hconn: then G − e₀ would be connected", code="main", focus="cut",
        ranges=[("-- hence G − e₀ is connected",
                 "(G.deleteEdge e₀).connected_of_forall_path_to a hreach")],
        math=("If every vertex has a path to a, any two vertices x and y are joined: go from x "
              "to a, then from a to y. So G − e₀ would be connected."),
        screen=lambda ex, F: (
            f"In reality G − e₀ has {len(F['comps'])} component(s): "
            + " and ".join(fmt_set(c) for c in F["comps"])
            + (f". There is no path from {F['b']} to {F['a']} in G − e₀." if F["cut"] else
               ". It IS connected: e₀ is not a cut edge, so no contradiction arises.")),
        lean=("`have hconn : (G.deleteEdge e₀).Connected := …` records the fact, using the "
              "shared lemma `connected_of_forall_path_to` (next page) with the centre a. "
              "`X.f args` is Lean shorthand for `f X args`."),
    ),
    dict(
        part=P4, title="The shared lemma connected_of_forall_path_to", code="lemmas",
        focus="cut",
        ranges=[("theorem connected_of_forall_path_to", "exact G.path_trans p hcy")],
        math=("If every vertex is joined by a path to one fixed vertex c, the graph is "
              "connected: from x go to c, then from c to y (a path from y to c, reversed)."),
        screen=lambda ex, F: (
            "Bottom-left: in G − e₀ the vertices that can reach a are " +
            fmt_set(next(c for c in F["comps"] if F["a"] in c)) + "."),
        lean=("`path_symm` reverses an undirected path; `path_trans` joins a path x → y with a "
              "path y → z. Both are proved in Lemmas.lean by induction on paths. In this proof "
              "`intro x y` fixes two vertices, `obtain` takes the paths to c, and "
              "`exact G.path_trans p hcy` joins them."),
    ),
    dict(
        part=P4, title="exact he₀ hconn: the contradiction  ∎", code="main", focus="cut",
        ranges=[("-- but e₀ is a cut edge", "exact he₀ hconn")],
        math=("But e₀ is a cut edge: G − e₀ is NOT connected. Contradiction. So the supposed "
              "orientation cannot exist: G is not orientable. ∎"),
        screen=lambda ex, F: (
            _hyp_warning(F)
            + f"Consistent with the screen: {F['n_sc']} of {F['n_o']} choices of directions "
              "are strongly connected (computed)."),
        lean=("`he₀ : G.IsCutEdge e₀` unfolds to `¬ (G.deleteEdge e₀).Connected`, i.e. "
              "`(G.deleteEdge e₀).Connected → False`. Applying it to `hconn` gives `False`, "
              "which is exactly the goal, so `exact he₀ hconn` ends the proof."),
    ),
    dict(
        part=P5, title="Contrast and checks: examples vs. proof", code="main", focus="reach",
        anchors=[],
        math=("Without a cut edge an orientation can exist: on the 6-cycle ('Next graph'), "
              "arrows all the way round are strongly connected. The theorem only rules out "
              "graphs WITH a cut edge. Every picture is one example. The script also checked "
              "every simple graph with up to 5 vertices; that is evidence, not a proof. The "
              "Lean proof covers every graph."),
        screen=lambda ex, F: (
            f"Checked by this script: all {ex.stats['n_graphs']:,} simple graphs on 1–5 "
            f"vertices; the {ex.stats['n_cut']:,} with a cut edge have 0 strongly connected "
            f"choices among {ex.stats['n_orient_checked']:,}; the lemma's conversion was "
            f"verified on {ex.stats['n_conv']:,} paths (graphs on 1–4 vertices)."),
        lean=("`#print axioms GraphCh10.supp39` lists only Lean's standard axioms (propext, "
              "Classical.choice, Quot.sound), with no `sorry` and no project axiom. The file "
              "status stays UNFINISHED until the project owner marks it."),
    ),
]


# ---------------------------------------------------------------------------
# 9. The interactive explorer
# ---------------------------------------------------------------------------

class Explorer:
    """Interactive companion: direct the edges, choose x, walk the lemma, step the proof."""

    MAX_CODE_LINES = 30

    def __init__(self, stats: dict):
        self.stats = stats
        self.lean = read_lean_sources()
        self._check_anchors()
        self.step = 0
        self.seed = 0
        self.message = ""
        self.load_example(0, redraw=False)

        for key in ("keymap.back", "keymap.forward"):  # free ← / → for the walkthrough
            plt.rcParams[key] = [k for k in plt.rcParams[key] if k not in ("left", "right")]

        self.fig = plt.figure(figsize=(19, 11.8), facecolor="white")
        try:
            self.fig.canvas.manager.set_window_title("Supp. 39: a cut edge prevents orientations")
        except AttributeError:
            pass
        self.fig.text(0.012, 0.975, "Supplementary Exercise 39:  a graph with a cut edge is "
                      "not orientable", fontsize=18, fontweight="bold", color=COLOR_TEXT,
                      va="center")
        self.fig.text(0.012, 0.946, "An interactive companion to the Lean proof GraphCh10.supp39. "
                      "The arrows are always a REAL attempt; the proof's 'suppose an orientation "
                      "exists' cannot be drawn.", fontsize=10.5, color=COLOR_WARN, style="italic",
                      va="center")
        self.fig.text(0.012, 0.919, "Click a vertex to choose x.   Click an edge to reverse it.",
                      fontsize=10, color="#444444", va="center")

        self.ax_graph = self.fig.add_axes([0.012, 0.495, 0.475, 0.375])
        self.caption = self.fig.text(0.2495, 0.895, "", ha="center", va="center", fontsize=11,
                                     fontweight="bold", color=COLOR_TEXT)
        self.ax_legend = self.fig.add_axes([0.012, 0.445, 0.475, 0.05])
        self.ax_minus = self.fig.add_axes([0.012, 0.165, 0.235, 0.27])
        self.ax_status = self.fig.add_axes([0.255, 0.165, 0.232, 0.27])
        self.ax_text = self.fig.add_axes([0.505, 0.565, 0.48, 0.36])
        self.ax_code = self.fig.add_axes([0.505, 0.105, 0.48, 0.445])
        for ax in (self.ax_legend, self.ax_minus, self.ax_status, self.ax_text, self.ax_code):
            ax.axis("off")

        def button(rect, label, cb, color="#F0F0F0", size=10):
            b = Button(self.fig.add_axes(rect), label, color=color, hovercolor="#DDE8F5")
            b.label.set_fontsize(size)
            b.on_clicked(cb)
            return b

        w, gap, x0 = 0.112, 0.0097, 0.012
        xs = [x0 + i * (w + gap) for i in range(4)]
        self.btn_graph = button([xs[0], 0.095, w, 0.045], "Next graph", lambda _e: self.next_graph())
        self.btn_e0 = button([xs[1], 0.095, w, 0.045], "Next e₀", lambda _e: self.next_e0())
        self.btn_flip = button([xs[2], 0.095, w, 0.045], "Flip e₀", lambda _e: self.flip_e0(),
                               color="#F7E1E4")
        self.btn_reset = button([xs[3], 0.095, w, 0.045], "Reset", lambda _e: self.reset(),
                                color="#E3EEDF")
        self.btn_random = button([xs[0], 0.04, w, 0.045], "Random arrows",
                                 lambda _e: self.randomize())
        self.btn_mode = button([xs[1], 0.04, w, 0.045], "", lambda _e: self.toggle_mode())
        self.btn_walk = button([xs[2], 0.04, w + gap + w, 0.045], "Walk the path ▶  (one edge)",
                               lambda _e: self.walk_step(), color="#E6F0FB")

        self.btn_prev = button([0.505, 0.035, 0.09, 0.055], "◀ Previous", lambda _e: self.go(-1))
        self.btn_next = button([0.705, 0.035, 0.09, 0.055], "Next ▶", lambda _e: self.go(+1),
                               color="#E3EEDF")
        self.step_label = self.fig.text(0.65, 0.0625, "", ha="center", va="center", fontsize=11,
                                        fontweight="bold", color=COLOR_TEXT)
        self.msg_label = self.fig.text(0.805, 0.0625, "", ha="left", va="center", fontsize=9.5,
                                       color="#555555", style="italic")

        self._draw_legend()
        self.fig.canvas.mpl_connect("button_press_event", self._on_click)
        self.fig.canvas.mpl_connect("key_press_event", self._on_key)
        self.enter_step(0)

    # -- state --------------------------------------------------------------

    def _check_anchors(self) -> None:
        for s in STEPS:
            lines = self.lean[s["code"]]
            for sub in s.get("anchors", []):
                n = sum(sub in ln for ln in lines)
                assert n == 1, f"anchor {sub!r} matches {n} lines of {s['code']}"
            for a, b in s.get("ranges", []):
                n = sum(a in ln for ln in lines)
                assert n == 1, f"range start {a!r} matches {n} lines of {s['code']}"
                i = next(i for i, ln in enumerate(lines) if a in ln)
                assert any(b in ln for ln in lines[i:]), f"range end {b!r} not after {a!r}"

    def highlighted(self, s: dict) -> list[int]:
        lines = self.lean[s["code"]]
        idx = {i for a in s.get("anchors", []) for i, ln in enumerate(lines) if a in ln}
        for a, b in s.get("ranges", []):
            i = next(i for i, ln in enumerate(lines) if a in ln)
            j = next(j for j in range(i, len(lines)) if b in lines[j])
            idx |= set(range(i, j + 1))
        return sorted(idx)

    def load_example(self, k: int, redraw: bool = True) -> None:
        self.ex_idx = k
        d = EXAMPLES[k]
        self.ex_def = d
        self.o: Orient = dict(d["orient"])
        self.e0 = edge_name(*d["e0"])
        self.x = d["x"]
        self.mode = "shortest"
        self.walk: int | None = None
        if redraw:
            self.redraw()

    @property
    def pos(self):
        return self.ex_def["pos"]

    def facts(self) -> dict:
        return compute_facts(self.ex_def, self.o, self.e0, self.x, self.mode)

    def walk_k(self, F: dict) -> int:
        """How many cases of the lemma's recursion are shown (all, unless walking)."""
        n = len(F["trace"])
        return n if self.walk is None else min(self.walk, n)

    def e0_choices(self) -> list[str]:
        cuts = cut_edges(self.ex_def["vs"], self.ex_def["ends"])
        return cuts or list(self.ex_def["ends"])

    def next_graph(self) -> None:
        self.load_example((self.ex_idx + 1) % len(EXAMPLES), redraw=False)
        self.message = f"graph: {self.ex_def['short']}"
        self.redraw()

    def next_e0(self) -> None:
        ch = self.e0_choices()
        self.e0 = ch[(ch.index(self.e0) + 1) % len(ch)] if self.e0 in ch else ch[0]
        self.walk = None
        self.message = f"e₀ is now {self.e0}"
        self.redraw()

    def flip(self, e: str) -> None:
        u, w = self.o[e]
        self.o = {**self.o, e: (w, u)}
        self.walk = None
        self.message = f"reversed {e}: now {w} → {u}"
        self.redraw()

    def flip_e0(self) -> None:
        self.flip(self.e0)

    def reset(self) -> None:
        self.load_example(self.ex_idx, redraw=False)
        self.message = "reset"
        self.redraw()

    def randomize(self) -> None:
        self.seed += 1
        rng = random.Random(39_000 + self.seed)
        self.o = {e: (u, w) if rng.random() < 0.5 else (w, u) for e, (u, w) in self.o.items()}
        self.walk = None
        self.message = "random arrows"
        self.redraw()

    def toggle_mode(self) -> None:
        self.mode = "via" if self.mode == "shortest" else "shortest"
        self.walk = None
        F = self.facts()
        self.message = ("path via e₀" if F["via_used"] else
                        "no directed path x → a uses e₀ here" if self.mode == "via" else
                        "shortest path")
        self.redraw()

    def walk_step(self) -> None:
        F = self.facts()
        n = len(F["trace"])
        if self.walk is None or self.walk >= n:
            self.walk = 0
        else:
            self.walk += 1
        self.message = f"walk: {self.walk} of {n}"
        self.redraw()

    def select_vertex(self, v: int) -> None:
        self.x, self.walk = v, None
        self.message = f"x = {v}"
        self.redraw()

    def go(self, delta: int) -> None:
        self.enter_step(max(0, min(len(STEPS) - 1, self.step + delta)))

    def enter_step(self, k: int) -> None:
        self.step = k
        self.redraw()

    # -- events -------------------------------------------------------------

    def _on_click(self, event) -> None:
        if event.inaxes is not self.ax_graph or event.button != 1 or event.xdata is None:
            return
        x, y = event.xdata, event.ydata
        pos = self.pos
        v = min(pos, key=lambda w: (pos[w][0] - x) ** 2 + (pos[w][1] - y) ** 2)
        if (pos[v][0] - x) ** 2 + (pos[v][1] - y) ** 2 <= (1.4 * NODE_R) ** 2:
            self.select_vertex(v)
            return
        best, dist = None, 0.2
        for e, (u, w) in self.o.items():
            (x1, y1), (x2, y2) = pos[u], pos[w]
            dx, dy = x2 - x1, y2 - y1
            t = ((x - x1) * dx + (y - y1) * dy) / (dx * dx + dy * dy)
            if not 0.1 <= t <= 0.9:
                continue
            d = abs((x - x1) * dy - (y - y1) * dx) / (dx * dx + dy * dy) ** 0.5
            if d < dist:
                best, dist = e, d
        if best is not None:
            self.flip(best)

    def _on_key(self, event) -> None:
        if event.key == "right":
            self.go(+1)
        elif event.key == "left":
            self.go(-1)

    # -- drawing ------------------------------------------------------------

    def redraw(self) -> None:
        s = STEPS[self.step]
        F = self.facts()
        self._draw_graph(s, F)
        self._draw_minus(s, F)
        self._draw_status(F)
        self._draw_text(s, F)
        self._draw_code(s)
        last = len(STEPS) - 1
        self.step_label.set_text(f"Page {self.step + 1} / {len(STEPS)}"
                                 + ("  (end)" if self.step == last else ""))
        for b, off, on_color in ((self.btn_prev, self.step == 0, "#F0F0F0"),
                                 (self.btn_next, self.step == last, "#E3EEDF")):
            b.label.set_alpha(0.3 if off else 1.0)
            b.color = "#F7F7F7" if off else on_color
            b.ax.set_facecolor(b.color)
        self.btn_mode.label.set_text("Path: via e₀" if self.mode == "shortest"
                                     else "Path: shortest")
        self.msg_label.set_text(f"[{self.message}]" if self.message else "")
        self.fig.canvas.draw_idle()

    def _tags(self, F: dict) -> dict:
        tags: dict[int, list[str]] = {}
        tags.setdefault(F["a"], []).append("a (tail)")
        tags.setdefault(F["b"], []).append("b (head)")
        tags.setdefault(F["x"], []).append("x")
        return {v: " · ".join(t) for v, t in tags.items()}

    def _path_styles(self, F: dict, first_only: bool = False) -> dict:
        """Blue: the directed path; green: edges the lemma has kept; gold: the e = e₀ case;
        dashed grey: edges dropped after reaching e₀."""
        st = {}
        path, tr = F["path"], F["trace"]
        if not path:
            return st
        k = self.walk_k(F)
        stop_at = next((i for i, (c, _e) in enumerate(tr) if c == "stop"), None)
        for i, (e, _u, _w) in enumerate(path):
            if first_only:
                if i == 0:
                    st[e] = dict(color=COLOR_FOCUS, lw=5.5, z=3, outline=True)
                continue
            if i < k and tr[i][0] == "keep":
                st[e] = dict(color=COLOR_KEEP, lw=5, z=3)
            elif i < k and tr[i][0] == "stop":
                st[e] = dict(color=COLOR_FOCUS, lw=5.5, z=3, outline=True)
            elif stop_at is not None and i > stop_at and k > stop_at:
                st.setdefault(e, dict(color="#BBBBBB", lw=3, ls=(0, (4, 3)), z=2.5))
            else:
                st.setdefault(e, dict(color=COLOR_PATH, lw=4.5, z=3))
        return st

    def _draw_graph(self, s: dict, F: dict) -> None:
        ax = self.ax_graph
        ax.clear()
        frame(ax)
        e0 = F["e0"]
        styles = {e0: dict(color=COLOR_CUT, lw=4.5, z=2.8)}
        focus = s["focus"]
        rings = {}
        if focus in ("dpath", "convert"):
            styles.update(self._path_styles(F))
        elif focus == "first":
            styles.update(self._path_styles(F, first_only=True))
        elif focus == "upath" and F["gpath"]:
            for e, _u, _w in F["gpath"]:
                styles[e] = dict(color=COLOR_KEEP, lw=5, z=3)
        if focus == "reach":
            rings = {v: COLOR_NOREACH for v in F["noreach"]}
        e0_label = "e₀ (cut edge)" if F["cut"] else "e₀ (NOT a cut edge)"
        draw_graph(ax, self.pos, F["ends"], o=F["o"], styles=styles, rings=rings,
                   tags=self._tags(F), elabels={e0: (e0_label, COLOR_CUT)})
        status = ("strongly connected ✓" if F["sc"] else
                  f"NOT strongly connected: no directed path {F['fail'][0]} → {F['fail'][1]}")
        self.caption.set_text(f"G = {F['name']}  ·  current arrows: {status}")

    def _draw_minus(self, s: dict, F: dict) -> None:
        ax = self.ax_minus
        ax.clear()
        frame(ax, (-3.4, 3.4), (-1.75, 2.25))
        vfill = {v: COMP_COLORS[i % len(COMP_COLORS)] for i, c in enumerate(F["comps"])
                 for v in c}
        styles = {}
        k_all = s["focus"] == "reach"
        if k_all:  # converted paths for every vertex with a directed path to a
            for v in F["reach"]:
                p = dpath(F["vs"], F["o"], v, F["a"])
                q, _tr = lemma_convert(F["o"], F["e0"], F["a"], p)
                for e, _u, _w in q:
                    styles[e] = dict(color=COLOR_KEEP, lw=4, z=3)
        elif F["conv"] is not None:
            k = self.walk_k(F)
            for i, (e, _u, _w) in enumerate(F["conv"]):
                if i < k:
                    styles[e] = dict(color=COLOR_KEEP, lw=4.5, z=3)
        draw_graph(ax, self.pos, F["ends"], styles=styles, removed=F["e0"], vfill=vfill,
                   rings={v: COLOR_NOREACH for v in F["noreach"]} if k_all else {},
                   tags={F["a"]: "a", **({F["x"]: "x"} if F["x"] != F["a"] else
                                         {F["a"]: "a = x"})},
                   r=0.3, fs=10.5, width=2.0, tag_fs=9.5)
        ax.text(0.5, 1.0, f"G − e₀: {len(F['comps'])} component(s)  ({'disconnected' if len(F['comps']) > 1 else 'connected'})",
                transform=ax.transAxes, ha="center", va="top", fontsize=10.5, fontweight="bold")
        sub = ("green: converted paths of all x that reach a" if k_all else
               "green: the converted path of x (the lemma's output)")
        ax.text(0.5, 0.0, sub + "; dotted: e₀ removed", transform=ax.transAxes, ha="center",
                va="bottom", fontsize=8.8, color="#444444")

    def _draw_status(self, F: dict) -> None:
        ax = self.ax_status
        ax.clear()
        ax.axis("off")
        ax.add_patch(plt.Rectangle((0, 0), 1, 1, transform=ax.transAxes, facecolor="#F7F7F7",
                                   edgecolor="#D0D0D0"))
        ok, no = "✓", "✗"
        rows = [
            ("Computed facts (Python model)", COLOR_TEXT, "bold"),
            (f"G simple {ok if F['simple'] else no}   G connected {ok if F['conn'] else no}",
             COLOR_TEXT, "normal"),
            (f"e₀ = {F['e0']}: " + (f"cut edge {ok}" if F["cut"] else f"NOT a cut edge {no}"),
             COLOR_CUT, "bold"),
            (f"e₀ points a = {F['a']} → b = {F['b']}", COLOR_TEXT, "normal"),
            (f"each edge has one of its directions {ok if F['dir_ok'] else no}", COLOR_TEXT,
             "normal"),
            ("strongly connected " + (ok if F["sc"] else
                                      f"{no}  (no path {F['fail'][0]} → {F['fail'][1]})"),
             COLOR_OK if F["sc"] else COLOR_WARN, "bold"),
            (f"directed path to a from {fmt_set(F['reach'])}", COLOR_TEXT, "normal"),
            (f"none to a from {fmt_set(F['noreach'])}", COLOR_WARN if F["noreach"] else COLOR_TEXT,
             "normal"),
            (f"all {F['n_o']} choices: {F['n_sc']} strongly connected", COLOR_TEXT, "normal"),
            ("⇒ G is " + ("orientable" if F["n_sc"] else "NOT orientable"),
             COLOR_OK if F["n_sc"] else COLOR_WARN, "bold"),
        ]
        step = 0.92 / len(rows)
        for i, (t, col, fw) in enumerate(rows):
            ax.text(0.04, 0.96 - i * step, t, transform=ax.transAxes, va="top", fontsize=9.6,
                    color=col, fontweight=fw)

    def _draw_legend(self) -> None:
        handles = [
            Line2D([], [], color=COLOR_CUT, linewidth=4, label="e₀"),
            Line2D([], [], color=COLOR_PATH, linewidth=4, label="directed path x → a"),
            Line2D([], [], color=COLOR_KEEP, linewidth=4, label="kept: path avoiding e₀"),
            Line2D([], [], color=COLOR_FOCUS, linewidth=4, label="first edge / case e = e₀"),
            Line2D([], [], color=COLOR_NOREACH, linewidth=2.4, linestyle="--",
                   label="ring: no directed path to a"),
        ]
        self.ax_legend.legend(handles=handles, loc="center", ncol=5, frameon=False,
                              fontsize=9.3, handlelength=1.8, columnspacing=1.0)

    def _draw_text(self, s: dict, F: dict) -> None:
        ax = self.ax_text
        ax.clear()
        ax.axis("off")
        math_txt = s["math"] if isinstance(s["math"], str) else s["math"](self, F)
        blocks = [("Graph theory", math_txt.replace("`", ""), COLOR_VERTEX),
                  ("On the screen now (computed)", s["screen"](self, F).replace("`", ""),
                   "#B5651D"),
                  ("Lean syntax", s["lean"].replace("`", ""), COLOR_OK)]
        height_pt = ax.get_position().height * self.fig.get_figheight() * 72
        for size in (11.5, 11, 10.5, 10, 9.5, 9, 8.5, 8):
            width = int(118 * 10 / size)
            wrapped = [(h, [ln for para in t.split("\n") for ln in textwrap.wrap(para, width)], c)
                       for h, t, c in blocks]
            n_lines = 1.3 + 1.9 + sum(1.25 + len(w) + 0.55 for _h, w, _c in wrapped)
            if n_lines * size * 1.42 <= height_pt:
                break
        self.text_fontsize = size
        line = size * 1.42 / height_pt
        y = 1.0
        ax.text(0, y, s["part"].upper(), transform=ax.transAxes, fontsize=size - 0.5,
                color="#777777", va="top", fontweight="bold")
        y -= 1.3 * line
        ax.text(0, y, s["title"], transform=ax.transAxes, fontsize=size + 4, va="top",
                fontweight="bold", color=COLOR_TEXT)
        y -= 1.9 * line
        for head, lines, col in wrapped:
            ax.text(0, y, head, transform=ax.transAxes, fontsize=size, va="top",
                    fontweight="bold", color=col)
            y -= 1.25 * line
            ax.text(0, y, "\n".join(lines), transform=ax.transAxes, fontsize=size, va="top",
                    color=COLOR_TEXT, linespacing=1.42)
            y -= (len(lines) + 0.55) * line

    def code_window(self, s: dict) -> tuple[int, int]:
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
        ax.text(0.012, 0.98, f"Lean source: {SOURCE_NAMES[s['code']]}  (read from disk; "
                "highlighted = this step)", transform=ax.transAxes, fontsize=9.5,
                fontweight="bold", va="top", color="#555555")
        n = max(len(rows), 22)
        step_y = 0.91 / n
        fontsize = 9 if n <= 26 else 8.4
        for r, (i, ln) in enumerate(rows):
            is_hl = i is not None and i in hl
            y = 0.935 - r * step_y
            if is_hl:
                ax.add_patch(plt.Rectangle((0.006, y - step_y * 0.95), 0.988, step_y * 0.98,
                                           transform=ax.transAxes, facecolor=COLOR_CODE_HL,
                                           edgecolor=COLOR_FOCUS, linewidth=1))
            comment = ln.strip().startswith("--") or i is None
            ax.text(0.012, y, ln if ln else " ", transform=ax.transAxes, va="top",
                    fontsize=fontsize, family="DejaVu Sans Mono",
                    color=COLOR_TEXT if is_hl or not comment else "#6A737D",
                    fontweight="bold" if is_hl else "normal")


# ---------------------------------------------------------------------------
# 10. Headless self-test of the explorer (--snapshots)
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


def _check_layout(ex: Explorer) -> None:
    """No text runs past the bottom or right edge of its panel; the axes do not overlap."""
    ex.fig.canvas.draw()
    renderer = ex.fig.canvas.get_renderer()
    for ax in (ex.ax_text, ex.ax_code, ex.ax_status, ex.ax_minus):
        box = ax.get_window_extent(renderer)
        for t in ax.texts:
            if not t.get_text().strip():
                continue
            bb = t.get_window_extent(renderer)
            assert bb.y0 >= box.y0 - 2 and bb.x1 <= box.x1 + 2 and bb.x0 >= box.x0 - 2, \
                f"text overflows its panel: {t.get_text()[:60]!r}"
    # the graph caption and the step texts stay inside the figure
    fb = ex.fig.bbox
    for t in ex.fig.texts:
        if t.get_text().strip():
            bb = t.get_window_extent(renderer)
            assert bb.x0 >= fb.x0 and bb.x1 <= fb.x1, f"figure text cut off: {t.get_text()[:60]!r}"


def self_test(ex: Explorer, outdir: Path) -> None:
    outdir.mkdir(parents=True, exist_ok=True)
    # 1. Every step renders on every example, text and code fit; one PNG per step (example 1).
    for k, s in enumerate(STEPS):
        for gi in (1, 2, 0):
            ex.load_example(gi, redraw=False)
            ex.enter_step(k)
            _check_layout(ex)
        a, b = ex.code_window(s)
        assert all(a <= i < b for i in ex.highlighted(s)), f"step {k + 1}: highlight off-screen"
        assert ex.highlighted(s) or s["part"] == P5, f"step {k + 1}: no code highlighted"
        ex.fig.savefig(outdir / f"step_{k + 1:02d}.png", dpi=80)
    ex.load_example(0, redraw=False)
    # 2. Next / Previous buttons and the arrow keys.
    ex.enter_step(0)
    _click(ex, ex.btn_next)
    assert ex.step == 1, "Next button did not advance"
    _click(ex, ex.btn_prev)
    assert ex.step == 0, "Previous button did not go back"
    _click(ex, ex.btn_prev)
    assert ex.step == 0
    _key(ex, "right")
    _key(ex, "right")
    assert ex.step == 2, "→ key did not advance"
    _key(ex, "left")
    assert ex.step == 1, "← key did not go back"
    ex.enter_step(len(STEPS) - 1)
    _click(ex, ex.btn_next)
    assert ex.step == len(STEPS) - 1
    # 3. Clicking a vertex chooses x; the conversion of its path is a path in G − e₀.
    conv_step = next(i for i, s in enumerate(STEPS) if s["title"].startswith("Key step"))
    ex.enter_step(conv_step)
    for v in ex.ex_def["vs"]:
        _press(ex.fig, ex.ax_graph, *ex.pos[v])
        assert ex.x == v, "vertex click did not choose x"
        F = ex.facts()
        if F["path"] is not None:
            assert is_upath(F["minus"], F["conv"], v, F["a"])
        else:
            assert v in F["noreach"] and v not in F["reach"]
    _press(ex.fig, ex.ax_graph, *ex.pos[0])
    ex.fig.savefig(outdir / "click_vertex_0.png", dpi=80)
    # ... the far side has no path; that is shown, not hidden.
    _press(ex.fig, ex.ax_graph, *ex.pos[4])
    F = ex.facts()
    assert F["path"] is None and "NO directed path" in STEPS[conv_step]["screen"](ex, F)
    ex.fig.savefig(outdir / "click_vertex_4_no_path.png", dpi=80)
    # 4. Walking the path edge by edge.
    _press(ex.fig, ex.ax_graph, *ex.pos[0])
    F = ex.facts()
    n = len(F["trace"])
    for i in range(n + 1):
        _click(ex, ex.btn_walk)
        assert ex.walk == i
        _check_layout(ex)
        ex.fig.savefig(outdir / f"walk_{i}.png", dpi=80)
    _click(ex, ex.btn_walk)
    assert ex.walk == 0
    # 5. Clicking an edge reverses it; still never strongly connected (cut edge).
    ex.reset()
    reach_step = next(i for i, s in enumerate(STEPS) if s["title"].startswith("Where it breaks"))
    ex.enter_step(reach_step)
    e = "{4,5}"
    (x1, y1), (x2, y2) = ex.pos[4], ex.pos[5]
    before = ex.o[e]
    _press(ex.fig, ex.ax_graph, (x1 + x2) / 2, (y1 + y2) / 2)
    assert ex.o[e] == before[::-1], "clicking an edge did not reverse it"
    assert not ex.facts()["sc"]
    ex.fig.savefig(outdir / "click_edge_flip.png", dpi=80)
    o_before = dict(ex.o)
    _press(ex.fig, ex.ax_graph, 0.0, 1.7)  # empty space: nothing changes
    assert ex.o == o_before
    # 6. Flip e₀: a and b swap, the red set moves to the other side.
    ex.reset()
    F0 = ex.facts()
    _click(ex, ex.btn_flip)
    F1 = ex.facts()
    assert (F1["a"], F1["b"]) == (F0["b"], F0["a"])
    assert F1["noreach"] and not F1["sc"]
    ex.fig.savefig(outdir / "flip_e0.png", dpi=80)
    # 7. Random arrows (many): never strongly connected while there is a cut edge.
    for _ in range(25):
        _click(ex, ex.btn_random)
        F = ex.facts()
        assert directions_ok(F["ends"], F["o"]) and not F["sc"] and F["noreach"]
    ex.fig.savefig(outdir / "random_arrows.png", dpi=80)
    # 8. Next graph → triangle with a tail; Next e₀ cycles through its two cut edges.
    _click(ex, ex.btn_graph)
    assert ex.ex_idx == 1
    seen = set()
    for _ in range(2):
        _click(ex, ex.btn_e0)
        seen.add(ex.e0)
        assert ex.facts()["cut"]
    assert seen == {"{2,3}", "{3,4}"}
    ex.fig.savefig(outdir / "graph_tail_e0_34.png", dpi=80)
    # 9. Contrast: the 6-cycle has no cut edge and its starting arrows are an orientation.
    _click(ex, ex.btn_graph)
    assert ex.ex_idx == 2
    F = ex.facts()
    assert not F["hyp"] and F["sc"] and F["n_sc"] == 2
    # ... and a path through e₀ exercises the lemma's e = e₀ case.
    ex.enter_step(next(i for i, s in enumerate(STEPS) if s["title"].startswith("Case e = e₀")))
    _click(ex, ex.btn_mode)
    F = ex.facts()
    assert F["via_used"] and any(c == "stop" for c, _e in F["trace"])
    assert is_upath(F["minus"], F["conv"], F["x"], F["a"])
    ex.fig.savefig(outdir / "contrast_via_e0.png", dpi=80)
    for i in range(len(F["trace"]) + 1):
        _click(ex, ex.btn_walk)
    ex.fig.savefig(outdir / "contrast_via_e0_walked.png", dpi=80)
    # ... in the cut-edge example, 'via e₀' is honestly reported as impossible.
    _click(ex, ex.btn_graph)
    assert ex.ex_idx == 0
    _click(ex, ex.btn_mode)
    F = ex.facts()
    assert ex.mode == "via" and F["via"] is None and not F["via_used"]
    _click(ex, ex.btn_reset)
    assert ex.mode == "shortest" and ex.o == EXAMPLES[0]["orient"]
    print(f"Explorer self-test passed: {len(STEPS)} steps rendered on all 3 graphs (text and "
          f"code fit), buttons, keys, vertex and edge clicks, walk, flip, random, next e₀, "
          f"contrast graph; snapshots in {outdir}")


# ---------------------------------------------------------------------------
# 11. Entry point
# ---------------------------------------------------------------------------

def main() -> None:
    try:
        sys.stdout.reconfigure(encoding="utf-8")
    except (AttributeError, ValueError):
        pass
    parser = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    parser.add_argument("--static", action="store_true",
                        help="only run the checks and save the PNG (no window)")
    parser.add_argument("--snapshots", metavar="DIR", type=Path,
                        help="headless self-test of the explorer; save one PNG per step")
    args = parser.parse_args()

    stats = run_checks()
    for d in stats["per_example"]:
        print(f"{d['name']}: {d['m']} edges, cut edges {d['cuts'] or 'none'}, "
              f"{d['n_sc']} of {d['n_o']} direction choices strongly connected")
    print(f"All assertions passed (approved statements; examples exhaustively; all "
          f"{stats['n_graphs']:,} simple graphs on 1..5 vertices: {stats['n_cut']:,} with a cut "
          f"edge, {stats['n_orient_checked']:,} of their direction choices, none strongly "
          f"connected; lemma conversion verified on {stats['n_conv']:,} paths).")

    out = Path(__file__).resolve().parent / "supp39.png"
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
