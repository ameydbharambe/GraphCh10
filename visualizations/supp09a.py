"""Visualization for Rosen Ch. 10, Supplementary Exercise 9(a):  N(A ∪ B) = N(A) ∪ N(B).

An EDUCATIONAL COMPANION to the Lean theorem `GraphCh10.supp09a`
(GraphCh10/Exercises/Supp09a.lean), for students learning Lean 4 and introductory graph
theory. It has two parts:

1. A static summary figure (visualizations/supp09a.png) for one fixed example.
2. An interactive explorer: click vertices to choose A and B, watch every neighborhood
   being recomputed, and step through the actual Lean proof with Previous/Next. Each step
   explains the mathematics and the Lean tactic and highlights the matching vertices,
   edges and witnesses. The Lean code shown is read from the project files at runtime.

This script only illustrates and checks ONE concrete graph. The general statement, for
every undirected graph and all vertex sets A and B, is established by the Lean proof,
not by this script.

The graph model follows GraphCh10/Definitions.lean exactly:

* `UGraph V E` -- vertices V, edges E, and `ends : E → Sym2 V`, the set {u, w} with one
  or two elements associated to each edge. Here `ends[e]` is a frozenset of size 1
  (a loop) or 2. Distinct edges may share the same ends (multiple edges).
* `Adj u w := ∃ e : E, G.ends e = s(u, w)` -- `adj(u, w)` below. A loop at v makes v
  adjacent to itself.
* `nbhd v := {u | G.Adj v u}` -- `nbhd(v)` below (N(v), used to explain adjacency).
* `nbhdSet A := {u | ∃ a ∈ A, G.Adj a u}` -- `nbhd_set(A)` below.

Every neighborhood is COMPUTED from `ends` with these definitions; none is hardcoded.

Run (from the project root):
    python -m pip install networkx matplotlib
    python visualizations/supp09a.py              # save the PNG, then open the explorer
    python visualizations/supp09a.py --static     # only checks + PNG (no window)
    python visualizations/supp09a.py --snapshots DIR
        # headless self-test: drives the explorer through every walkthrough step,
        # simulates mouse clicks, and saves one PNG per step into DIR

Explorer controls:
    click a vertex          cycle its membership: none → A → B → both → none
    "Highlight" buttons     show N(A), N(B), N(A ∪ B) (left side) or N(A) ∪ N(B) (right side)
    ◀ Previous / Next ▶     move through the walkthrough (also ← / → keys)
    Next example            show another vertex / witness for the current step
    Reset A, B / Clear A, B restore the starting example / make both sets empty
"""

from __future__ import annotations

import argparse
import sys
import textwrap
from itertools import combinations
from pathlib import Path

import matplotlib

# Pick a file-only backend before pyplot is imported when no window will be opened.
if "--static" in sys.argv or "--snapshots" in sys.argv:
    matplotlib.use("Agg")

import matplotlib.patheffects as pe
import matplotlib.pyplot as plt
import networkx as nx
from matplotlib.backend_bases import MouseEvent
from matplotlib.gridspec import GridSpec
from matplotlib.lines import Line2D
from matplotlib.patches import Circle, FancyArrowPatch, Patch, Wedge
from matplotlib.widgets import Button, RadioButtons

PROJECT_ROOT = Path(__file__).resolve().parent.parent
PROOF_FILE = PROJECT_ROOT / "GraphCh10" / "Exercises" / "Supp09a.lean"
DEFS_FILE = PROJECT_ROOT / "GraphCh10" / "Definitions.lean"

# ---------------------------------------------------------------------------
# 1. The concrete graph G = (V, E, ends), mirroring `UGraph V E`
# ---------------------------------------------------------------------------

V: list[str] = ["a", "b", "c", "d", "e", "f", "g", "h", "i"]

# ends : E → Sym2 V.  Each value is the set {u, w}; a one-element set is a loop.
ends: dict[str, frozenset[str]] = {
    "e1": frozenset({"a", "e"}),
    "e2": frozenset({"a", "f"}),
    "e3": frozenset({"b", "f"}),
    "e4": frozenset({"b", "c"}),
    "e5": frozenset({"c", "g"}),
    "e6": frozenset({"d", "g"}),
    "e7": frozenset({"d", "h"}),
    "e8": frozenset({"d", "h"}),  # a second edge with the same ends as e7 (multiple edges)
    "e9": frozenset({"c", "f"}),
    "e10": frozenset({"d"}),  # a loop at d: the set {d} has one element
    "e11": frozenset({"e", "i"}),
}
E: list[str] = list(ends)

# The two nonempty vertex subsets of the starting example.
A: frozenset[str] = frozenset({"a", "b"})
B: frozenset[str] = frozenset({"c", "d"})


def sym2(u: str, w: str) -> frozenset[str]:
    """s(u, w): the unordered pair {u, w} (a single element when u = w)."""
    return frozenset({u, w})


def adj_edges(u: str, w: str) -> list[str]:
    """All edges e with ends e = s(u, w): the possible witnesses for `Adj u w`."""
    return [e for e in E if ends[e] == sym2(u, w)]


def adj(u: str, w: str) -> bool:
    """`Adj u w := ∃ e : E, G.ends e = s(u, w)`."""
    return len(adj_edges(u, w)) > 0


def nbhd(v: str) -> frozenset[str]:
    """`nbhd v := {u | G.Adj v u}`: N(v), the vertices adjacent to v."""
    return frozenset(u for u in V if adj(v, u))


def nbhd_set(S: frozenset[str]) -> frozenset[str]:
    """`nbhdSet S := {u | ∃ a ∈ S, G.Adj a u}`, computed directly from the definition."""
    return frozenset(u for u in V if any(adj(a, u) for a in S))


def witnesses(S: frozenset[str], u: str) -> list[tuple[str, str]]:
    """All (a, e) with a ∈ S and ends e = s(a, u): the witnesses of `u ∈ nbhdSet S`."""
    return [(a, e) for a in sorted(S) for e in adj_edges(a, u)]


# ---------------------------------------------------------------------------
# 2. The four sets in the identity (starting example)
# ---------------------------------------------------------------------------

A_union_B = A | B
N_A = nbhd_set(A)
N_B = nbhd_set(B)
LHS = nbhd_set(A_union_B)  # N(A ∪ B)
RHS = N_A | N_B  # N(A) ∪ N(B)


# ---------------------------------------------------------------------------
# 3. Programmatic checks
# ---------------------------------------------------------------------------

def check_identity(SA: frozenset[str], SB: frozenset[str]) -> tuple[frozenset, frozenset]:
    """For the given A and B: assert both inclusions witness-by-witness and the identity.
    Returns (N(A ∪ B), N(A) ∪ N(B))."""
    na, nb, union = nbhd_set(SA), nbhd_set(SB), SA | SB
    lhs, rhs = nbhd_set(union), na | nb

    # Forward inclusion, as in `forward`: a witness a ∈ A ∪ B lies in A or in B
    # (`rcases haAB with haA | haB`), and the same witness puts u in N(A) or in N(B).
    for u in lhs:
        for a, _e in witnesses(union, u):
            assert (a in SA and u in na) or (a in SB and u in nb)
        assert u in rhs

    # Backward inclusion, as in `backward`: a witness in A (or in B) is also a witness
    # in A ∪ B (`Or.inl haA` / `Or.inr hbB`), with the same adjacency `hadj`.
    for u in rhs:
        ws = witnesses(SA, u) + witnesses(SB, u)
        assert ws, f"{u} ∈ N(A) ∪ N(B) needs a witness"
        for a, e in ws:
            assert a in union and ends[e] == sym2(a, u)
        assert u in lhs

    assert lhs == rhs, f"N(A ∪ B) = {sorted(lhs)} but N(A) ∪ N(B) = {sorted(rhs)}"
    return lhs, rhs


def run_checks() -> int:
    """Assert the identity and the two inclusions on this graph; return #subset pairs checked."""
    # Well-formedness of the UGraph model: every edge has a set of one or two vertices of V.
    assert all(1 <= len(ends[e]) <= 2 and ends[e] <= set(V) for e in E)
    # Adj is symmetric, because s(u, w) = s(w, u).
    assert all(adj(u, w) == adj(w, u) for u in V for w in V)
    # N(v) agrees with N({v}).
    assert all(nbhd(v) == nbhd_set(frozenset({v})) for v in V)
    # The example is informative: A, B nonempty and the neighborhoods genuinely differ.
    assert A and B
    assert N_A - N_B and N_B - N_A and N_A & N_B, "want distinct, overlapping neighborhoods"
    assert set(V) - LHS, "want at least one vertex outside both neighborhoods"

    # Cross-check our `nbhdSet` against NetworkX's own adjacency on the same multigraph.
    G = to_networkx()
    for S in (A, B, A_union_B):
        nx_nbhd = frozenset(w for a in S for w in G.neighbors(a))
        assert nx_nbhd == nbhd_set(S), f"NetworkX disagrees on N({sorted(S)})"

    # Both inclusions and the identity on the starting example.
    lhs, rhs = check_identity(A, B)
    assert (lhs, rhs) == (LHS, RHS)

    # Extra: exhaustive check for EVERY pair of subsets of V in this one graph.
    # Each N(S) is computed from the definition, never from the identity being tested.
    subsets = [frozenset(c) for r in range(len(V) + 1) for c in combinations(V, r)]
    N = {S: nbhd_set(S) for S in subsets}
    for S in subsets:
        for T in subsets:
            assert N[S | T] == N[S] | N[T]
    return len(subsets) ** 2


def to_networkx() -> nx.MultiGraph:
    """The same graph as a NetworkX MultiGraph (edge keys are the edge names in E)."""
    G = nx.MultiGraph()
    G.add_nodes_from(V)
    for e in E:
        endpoints = sorted(ends[e])
        u, w = (endpoints * 2)[:2]  # a loop {v} becomes the pair (v, v)
        G.add_edge(u, w, key=e)
    return G


# ---------------------------------------------------------------------------
# 4. Shared drawing helpers
# ---------------------------------------------------------------------------

POS: dict[str, tuple[float, float]] = {
    "a": (0.0, 2.0), "b": (0.0, 0.0), "e": (1.2, 3.2), "f": (1.2, 1.0),
    "c": (2.4, 0.0), "g": (3.6, 1.0), "d": (3.6, 2.4), "h": (4.8, 2.4), "i": (2.6, 3.5),
}

COLOR_A = "#3B6FB6"  # blue: vertices of A, and witnesses in A
COLOR_B = "#E08A2C"  # orange: vertices of B, and witnesses in B
COLOR_AB = "#7B4FA0"  # purple: witnesses in A ∪ B (before splitting into cases)
COLOR_OTHER = "#E6E6E6"  # vertices in neither A nor B
COLOR_MEMBER = "#1E8C45"  # green ring: vertex belongs to the set shown in the panel
COLOR_FOCUS = "#F2B705"  # gold: the vertex / edges the current walkthrough step is about
COLOR_EDGE = "#B5B5B5"
COLOR_TEXT = "#222222"
COLOR_WARN = "#9A2A2A"
COLOR_CODE_BG = "#FBFBF8"
COLOR_CODE_HL = "#FFF1B8"

NODE_SIZE = 950
NODE_R = 0.25  # node radius in data units (interactive explorer)


def fill_color(v: str, SA: frozenset[str] = A, SB: frozenset[str] = B) -> str:
    """Vertex fill depends only on A and B, so it is identical in every panel."""
    if v in SA and v in SB:
        return COLOR_AB
    if v in SA:
        return COLOR_A
    if v in SB:
        return COLOR_B
    return COLOR_OTHER


def parallel_rad(e: str) -> float:
    """Curvature for edges sharing the same ends, so multiple edges are drawn apart."""
    group = [x for x in E if ends[x] == ends[e]]
    k, m = group.index(e), len(group)
    return (k - (m - 1) / 2) * 0.35


def draw_edges(ax, edge_colors: dict[str, str], emphasized: frozenset[str] = frozenset(),
               shrink: float = 14) -> None:
    """Draw every edge of G. `edge_colors` highlights edges; `emphasized` edges are drawn
    extra thick with a dark outline (the edge a walkthrough step is talking about)."""
    for e in E:
        color = edge_colors.get(e, COLOR_EDGE)
        width = 3.6 if e in edge_colors else 1.6
        z = 2 if e in edge_colors else 1
        effects = None
        if e in emphasized:
            width, z = 5.5, 2.5
            effects = [pe.withStroke(linewidth=8.5, foreground="#333333")]
        pts = sorted(ends[e])
        if len(pts) == 1:  # loop: a circle sitting on top of the vertex
            x, y = POS[pts[0]]
            patch = Circle((x, y + 0.32), 0.26, fill=False, edgecolor=color,
                           linewidth=width, zorder=z)
            lx, ly = x, y + 0.72
        else:
            (x1, y1), (x2, y2) = POS[pts[0]], POS[pts[1]]
            rad = parallel_rad(e)
            patch = FancyArrowPatch((x1, y1), (x2, y2), arrowstyle="-",
                                    connectionstyle=f"arc3,rad={rad}", color=color,
                                    linewidth=width, shrinkA=shrink, shrinkB=shrink, zorder=z)
            # midpoint of the quadratic Bézier used by arc3
            lx = (x1 + x2) / 2 + 0.5 * rad * (y2 - y1)
            ly = (y1 + y2) / 2 - 0.5 * rad * (x2 - x1)
        if effects:
            patch.set_path_effects(effects)
        ax.add_patch(patch)
        ax.text(lx, ly, e, fontsize=7.5, color="#555555", ha="center", va="center",
                zorder=3, bbox=dict(boxstyle="round,pad=0.12", fc="white", ec="none",
                                    alpha=0.85))


def witness_edges(S: frozenset[str], targets: frozenset[str],
                  color_of) -> dict[str, str]:
    """Color every edge that witnesses some u ∈ N(S), with color chosen by the witness a."""
    colors: dict[str, str] = {}
    for u in targets:
        for a, e in witnesses(S, u):
            colors.setdefault(e, color_of(a))
    return colors


def fmt(S) -> str:
    return "{" + ", ".join(sorted(S)) + "}" if S else "∅"


def fmt_w(ws: list[tuple[str, str]]) -> str:
    return ", ".join(f"{a} ({e})" for a, e in ws) if ws else "—"


# ---------------------------------------------------------------------------
# 5. Static summary figure (visualizations/supp09a.png)
# ---------------------------------------------------------------------------

def draw_graph(ax, members: frozenset[str], edge_colors: dict[str, str], title: str,
               subtitle: str) -> None:
    """Draw G with fixed positions. `members` get a green ring; `edge_colors` highlight
    witness edges (all other edges are light gray)."""
    draw_edges(ax, edge_colors)

    G = to_networkx()
    ring_colors = [COLOR_MEMBER if v in members else "#8C8C8C" for v in V]
    ring_widths = [4.0 if v in members else 1.0 for v in V]
    nodes = nx.draw_networkx_nodes(G, POS, nodelist=V, ax=ax, node_size=NODE_SIZE,
                                   node_color=[fill_color(v) for v in V],
                                   edgecolors=ring_colors, linewidths=ring_widths)
    nodes.set_zorder(4)
    labels = nx.draw_networkx_labels(
        G, POS, ax=ax, font_size=12, font_weight="bold",
        font_color={v: ("white" if v in A | B else COLOR_TEXT) for v in V})
    for t in labels.values():
        t.set_zorder(5)

    ax.set_title(title, fontsize=13, fontweight="bold", color=COLOR_TEXT, pad=22)
    ax.text(0.5, 1.015, subtitle, transform=ax.transAxes, ha="center", va="bottom",
            fontsize=9.5, color="#444444")
    ax.set_xlim(-0.6, 5.4)
    ax.set_ylim(-0.6, 4.2)
    ax.set_aspect("equal")
    ax.axis("off")


def build_figure(n_pairs: int) -> plt.Figure:
    fig = plt.figure(figsize=(19, 16.5), facecolor="white")
    gs = GridSpec(3, 3, figure=fig, height_ratios=[1, 1, 0.78], hspace=0.32, wspace=0.08,
                  left=0.03, right=0.97, top=0.865, bottom=0.03)

    fig.suptitle("Supplementary Exercise 9(a):  N(A ∪ B) = N(A) ∪ N(B)",
                 fontsize=19, fontweight="bold", color=COLOR_TEXT, y=0.985)
    fig.text(0.5, 0.955,
             "A concrete example illustrating the Lean theorem GraphCh10.supp09a.  "
             "Neighborhoods are computed from the definitions  Adj u w := ∃ e, ends e = s(u, w)  "
             "and  nbhdSet S := {u | ∃ a ∈ S, Adj a u}.",
             ha="center", fontsize=10.5, color="#444444")
    fig.text(0.5, 0.937,
             "One example only: it does not prove the theorem. The proof for every undirected "
             "graph and all A, B ⊆ V is the Lean proof.  "
             "Run  python visualizations/supp09a.py  for the interactive walkthrough.",
             ha="center", fontsize=10.5, color=COLOR_WARN, style="italic")

    color_by_set = lambda a: COLOR_A if a in A else COLOR_B  # noqa: E731

    ax = fig.add_subplot(gs[0, 0])
    draw_graph(ax, frozenset(), {}, "The graph G and the subsets A, B",
               f"A = {fmt(A)} (blue),  B = {fmt(B)} (orange).  e7, e8 are multiple edges; "
               "e10 is a loop at d")

    ax = fig.add_subplot(gs[0, 1])
    draw_graph(ax, N_A, witness_edges(A, N_A, lambda a: COLOR_A),
               f"N(A) = {fmt(N_A)}", "green ring = in N(A);  blue edge = Adj a u with a ∈ A")

    ax = fig.add_subplot(gs[0, 2])
    draw_graph(ax, N_B, witness_edges(B, N_B, lambda a: COLOR_B),
               f"N(B) = {fmt(N_B)}", "green ring = in N(B);  orange edge = Adj b u with b ∈ B")

    ax = fig.add_subplot(gs[1, 0])
    draw_graph(ax, LHS, witness_edges(A_union_B, LHS, lambda a: COLOR_AB),
               f"Left side:  N(A ∪ B) = {fmt(LHS)}",
               "purple edge = Adj a u with a ∈ A ∪ B  (one witness set, no case split yet)")

    ax = fig.add_subplot(gs[1, 1])
    draw_graph(ax, RHS, witness_edges(A_union_B, RHS, color_by_set),
               f"Right side:  N(A) ∪ N(B) = {fmt(RHS)}",
               "the same edges, now colored by the case  a ∈ A (blue)  or  a ∈ B (orange)")

    # Membership table: every vertex, its witnesses, and both sides.
    ax = fig.add_subplot(gs[1, 2])
    ax.axis("off")
    rows = []
    for u in V:
        rows.append([u, fmt_w(witnesses(A, u)), fmt_w(witnesses(B, u)),
                     "✓" if u in LHS else "✗", "✓" if u in RHS else "✗"])
    table = ax.table(cellText=rows,
                     colLabels=["u", "witnesses in A", "witnesses in B",
                                "u ∈ N(A∪B)", "u ∈ N(A)∪N(B)"],
                     loc="center", cellLoc="center",
                     colWidths=[0.06, 0.24, 0.27, 0.205, 0.245])
    table.auto_set_font_size(False)
    table.set_fontsize(9.5)
    table.scale(1, 1.55)
    for (r, c), cell in table.get_celld().items():
        cell.set_edgecolor("#CCCCCC")
        if r == 0:
            cell.set_facecolor("#EFEFEF")
            cell.set_text_props(fontweight="bold")
        elif c == 0:
            cell.set_facecolor(fill_color(V[r - 1]))
            cell.set_text_props(fontweight="bold",
                                color="white" if V[r - 1] in A | B else COLOR_TEXT)
        elif c in (3, 4):
            ok = rows[r - 1][c] == "✓"
            cell.set_text_props(color=COLOR_MEMBER if ok else COLOR_WARN, fontweight="bold")
    ax.set_title("Membership and witnesses (computed)", fontsize=13, fontweight="bold",
                 color=COLOR_TEXT, pad=22)
    ax.text(0.5, 1.015, "a witness 'a (e)' means a ∈ S and ends e = s(a, u), so Adj a u",
            transform=ax.transAxes, ha="center", va="bottom", fontsize=9.5, color="#444444")

    # Proof correspondence panel.
    ax = fig.add_subplot(gs[2, :])
    ax.axis("off")
    ax.add_patch(plt.Rectangle((0, 0), 1, 1, transform=ax.transAxes, facecolor="#F7F7F7",
                               edgecolor="#D0D0D0", linewidth=1))

    fwd = ["Forward inclusion  (have forward : u ∈ N(A ∪ B) → u ∈ N(A) ∪ N(B))",
           "rintro ⟨a, haAB, hadj⟩ picks a witness a ∈ A ∪ B with Adj a u (a purple edge);",
           "rcases haAB with haA | haB splits on where a lies, recoloring the edge blue or orange:",
           ""]
    for u in sorted(LHS):
        a, e = witnesses(A_union_B, u)[0]
        if a in A:
            fwd.append(f"  u = {u}:  a = {a} via {e};  {a} ∈ A  ⇒  Or.inl ⟨{a}, haA, hadj⟩ : "
                       f"{u} ∈ N(A)")
        else:
            fwd.append(f"  u = {u}:  a = {a} via {e};  {a} ∈ B  ⇒  Or.inr ⟨{a}, haB, hadj⟩ : "
                       f"{u} ∈ N(B)")

    bwd = ["Backward inclusion  (have backward : u ∈ N(A) ∪ N(B) → u ∈ N(A ∪ B))",
           "rintro (⟨a, haA, hadj⟩ | ⟨b, hbB, hadj⟩) gets a witness in A or in B;",
           "the same vertex and the same edge witness u ∈ N(A ∪ B) (Or.inl haA / Or.inr hbB):",
           ""]
    for u in sorted(RHS):
        ws = witnesses(A, u)
        if ws:
            a, e = ws[0]
            bwd.append(f"  u = {u}:  {u} ∈ N(A) via {a} ({e})  ⇒  ⟨{a}, Or.inl haA, hadj⟩ : "
                       f"{u} ∈ N(A ∪ B)")
        else:
            b, e = witnesses(B, u)[0]
            bwd.append(f"  u = {u}:  {u} ∈ N(B) via {b} ({e})  ⇒  ⟨{b}, Or.inr hbB, hadj⟩ : "
                       f"{u} ∈ N(A ∪ B)")

    for x, lines in ((0.015, fwd), (0.515, bwd)):
        ax.text(x, 0.94, lines[0], transform=ax.transAxes, fontsize=11.5, fontweight="bold",
                va="top", color=COLOR_TEXT)
        ax.text(x, 0.835, "\n".join(lines[1:]), transform=ax.transAxes, fontsize=10,
                va="top", color=COLOR_TEXT, family="DejaVu Sans Mono", linespacing=1.45)

    ax.text(0.5, 0.05,
            f"Checked by assertions in this script: N(A ∪ B) = N(A) ∪ N(B) = {fmt(LHS)}; "
            f"both inclusions hold witness-by-witness; and, for this one graph only, the "
            f"identity holds for all {n_pairs:,} pairs of subsets (A, B).\n"
            f"Vertices a and i lie in neither side: no vertex of A ∪ B is adjacent to them.",
            transform=ax.transAxes, ha="center", fontsize=9.8, color="#333333")

    legend = [
        Patch(facecolor=COLOR_A, edgecolor="#8C8C8C", label="vertex in A"),
        Patch(facecolor=COLOR_B, edgecolor="#8C8C8C", label="vertex in B"),
        Patch(facecolor=COLOR_OTHER, edgecolor="#8C8C8C", label="vertex in neither"),
        Line2D([], [], marker="o", color="none", markerfacecolor="white",
               markeredgecolor=COLOR_MEMBER, markeredgewidth=3, markersize=13,
               label="green ring: in the panel's set"),
        Line2D([], [], color=COLOR_A, linewidth=3.5, label="witness edge from A"),
        Line2D([], [], color=COLOR_B, linewidth=3.5, label="witness edge from B"),
        Line2D([], [], color=COLOR_AB, linewidth=3.5, label="witness edge from A ∪ B"),
        Line2D([], [], color=COLOR_EDGE, linewidth=1.6, label="other edge"),
    ]
    fig.legend(handles=legend, loc="upper center", ncol=8, frameon=False, fontsize=10,
               bbox_to_anchor=(0.5, 0.927))
    return fig


# ---------------------------------------------------------------------------
# 6. Lean source, read from the project (the source of truth)
# ---------------------------------------------------------------------------

def read_lean_sources() -> dict[str, list[str]]:
    """The proof of `supp09a` and the definitions it uses, read verbatim from disk."""
    for path in (PROOF_FILE, DEFS_FILE):
        if not path.exists():
            sys.exit(f"error: cannot find {path}; run this script inside the GraphCh10 project")

    proof_lines = PROOF_FILE.read_text(encoding="utf-8").splitlines()
    start = next(i for i, ln in enumerate(proof_lines) if ln.startswith("theorem supp09a"))
    end = next(i for i, ln in enumerate(proof_lines)
               if i > start and "exact ⟨forward, backward⟩" in ln)
    proof = proof_lines[start:end + 1]

    def_lines = DEFS_FILE.read_text(encoding="utf-8").splitlines()

    def find(prefix: str) -> str:
        hits = [ln for ln in def_lines if ln.strip().startswith(prefix)]
        assert len(hits) == 1, f"expected exactly one line starting with {prefix!r}"
        return hits[0].rstrip()

    defs = [
        "-- GraphCh10/Definitions.lean (excerpt; docstrings omitted)",
        find("structure UGraph"),
        find("ends : E → Sym2 V"),
        "",
        "namespace UGraph   -- inside: variable (G : UGraph V E)",
        "",
        find("def Adj"),
        "",
        find("def nbhd (v : V)"),
        "",
        find("def nbhdSet"),
    ]
    return {"proof": proof, "defs": defs}


# ---------------------------------------------------------------------------
# 7. The walkthrough: graph basics, then the Lean proof line by line
# ---------------------------------------------------------------------------
# Each step: part, title, which code to show ("defs" or "proof"), substrings that pick
# the highlighted code lines, the view to switch to, a focus kind (what to highlight on
# the graph), and two explanations. `math` may be a function of (explorer, focus).

NO_CASE = ("With the current A and B no vertex goes through this case. "
           "Click vertices to change A or B and come back.")


def _yn(b: bool) -> str:
    return "yes" if b else "no"


STEPS: list[dict] = [
    dict(
        part="Part 1 · Graph basics", title="Vertices and edges", code="defs",
        anchors=["structure UGraph", "ends : E → Sym2 V"], view="none", focus="loop_multi",
        math=lambda ex, f: (
            "A graph has vertices (the circles a to i) and edges (the lines e1 to e11). "
            "Each edge has a set of endpoints. Usually the set has two vertices, like "
            "e4 = {b, c}. A loop has one: e10 = {d} joins d to itself. Different edges can "
            "have the same endpoints; e7 and e8 both join d and h (multiple edges). "
            "Both special cases are highlighted in gold."),
        lean=("`structure UGraph (V E)` has one field, `ends : E → Sym2 V`, which gives every "
              "edge its set of endpoints. `Sym2 V` is the type of unordered pairs: "
              "s(u, w) = s(w, u), and s(v, v) is the one-element set {v}. So loops and multiple "
              "edges are allowed: the theorem covers these graphs too."),
    ),
    dict(
        part="Part 1 · Graph basics", title="Adjacency and the neighbors of a vertex",
        code="defs", anchors=["def Adj", "def nbhd (v : V)"], view="none", focus="vertex_nbrs",
        math=lambda ex, f: (
            "Two vertices are adjacent when some edge joins them. The gold vertex v and its "
            "gold edges are shown; the green-ringed vertices are its neighbors "
            f"N(v). Here v = {f['v']}, and N({f['v']}) = {fmt(nbhd(f['v']))}. "
            "Press 'Next example' to move v. Because of the loop e10, d is adjacent to itself, "
            "so d ∈ N(d)."),
        lean=("`def Adj (u w : V) : Prop := ∃ e : E, G.ends e = s(u, w)`. It is a proposition "
              "(a statement): to prove `G.Adj u w` you must name an edge e and show its ends are "
              "{u, w}. Since s(u, w) = s(w, u), adjacency is symmetric. "
              "`nbhd v` is the set of all u with `G.Adj v u`."),
    ),
    dict(
        part="Part 1 · Graph basics", title="The neighborhood N(S) of a set S",
        code="defs", anchors=["def nbhdSet"], view="NA", focus=None,
        math=lambda ex, f: (
            "N(S) collects every vertex adjacent to at least one vertex of S. Each member u has "
            "a witness: a vertex a ∈ S joined to u by an edge (the coloured edges). Shown: "
            f"S = A = {fmt(ex.A)}, so N(A) = {fmt(nbhd_set(ex.A))}. "
            "A vertex of S can itself be in N(S), but only if it is adjacent to a vertex of S. "
            "Also N(∅) = ∅: with no vertices in S there are no witnesses."),
        lean=("`def nbhdSet (A : Set V) : Set V := {u | ∃ a ∈ A, G.Adj a u}`. "
              "So `u ∈ G.nbhdSet A` literally means `∃ a, a ∈ A ∧ G.Adj a u`. Lean unfolds "
              "this automatically, and the proof relies on that: tactics can take this "
              "existential apart, and build a new one."),
    ),
    dict(
        part="Part 1 · Graph basics", title="Try it: choose A and B yourself",
        code="proof", anchors=["theorem supp09a", "G.nbhdSet (A ∪ B) = G.nbhdSet A"],
        view="RHS", focus=None,
        math=lambda ex, f: (
            "Click any vertex to change its membership: none → A (blue) → B (orange) → "
            "both (half and half) → none. Use the 'Highlight' buttons to show N(A), N(B), the "
            "left side N(A ∪ B) or the right side N(A) ∪ N(B). After every click the panel "
            "under the graph recomputes all four sets from the edges. Try A = ∅, a single "
            "vertex, overlapping A and B, or every vertex."),
        lean=("The two sides always agree, and the theorem `supp09a` explains why: for every "
              "graph and every choice of A and B the sets are equal. The rest of this walkthrough "
              "goes through its proof one line at a time."),
    ),
    dict(
        part="Part 2 · The Lean proof", title="The theorem statement", code="proof",
        anchors=["theorem supp09a", "G.nbhdSet (A ∪ B) = G.nbhdSet A"], view="LHS", focus=None,
        math=lambda ex, f: (
            "Claim: for every undirected graph G with vertex type V and edge type E, and every "
            "pair of vertex sets A and B, N(A ∪ B) = N(A) ∪ N(B). Nothing is assumed about "
            "finiteness, loops or multiple edges."),
        lean=("`{V : Type u} {E : Type v}` are implicit arguments: Lean works them out from G. "
              "`(G : UGraph V E) (A B : Set V)` are explicit. `:= by` switches to tactic mode: "
              "each following line changes the current goal (what is left to prove) until no "
              "goals remain."),
    ),
    dict(
        part="Part 2 · The Lean proof", title="ext u: compare the two sets element by element",
        code="proof", anchors=["ext u", "two sets are equal when"], view="RHS", focus="ext",
        math=lambda ex, f: (
            "Two sets are equal exactly when they have the same elements. So fix any vertex u "
            "and show: u ∈ N(A ∪ B) if and only if u ∈ N(A) ∪ N(B). "
            f"Example shown: u = {f['u']}. Is u in the left side? {_yn(f['u'] in ex.lhs)}. "
            f"Is u in the right side? {_yn(f['u'] in ex.rhs)}. "
            "Press 'Next example' to try other vertices."),
        lean=("`ext u` uses set extensionality and names the arbitrary element u. The goal "
              "becomes `u ∈ G.nbhdSet (A ∪ B) ↔ u ∈ G.nbhdSet A ∪ G.nbhdSet B`. The picture "
              "checks one u at a time. In Lean, u is arbitrary, so the rest of the proof "
              "covers every vertex at once."),
    ),
    dict(
        part="Part 2 · The Lean proof", title="have forward: the inclusion ⊆", code="proof",
        anchors=["have forward", "(⊆) a vertex adjacent"], view="LHS", focus=None,
        math=lambda ex, f: (
            "First direction: every vertex of the left side N(A ∪ B) also lies in the right side "
            "N(A) ∪ N(B). Here every green-ringed vertex must turn out to be in N(A) or N(B)."),
        lean=("`have forward : P → Q := by …` proves an intermediate fact and gives it the name "
              "`forward`, so it can be used later. Its proof is the indented block underneath."),
    ),
    dict(
        part="Part 2 · The Lean proof", title="rintro ⟨a, haAB, hadj⟩: unpack the witness",
        code="proof", anchors=["rintro ⟨a, haAB, hadj⟩"], view="LHS", focus="fwd",
        math=lambda ex, f: (
            "Assume u ∈ N(A ∪ B). By definition there is a witness a ∈ A ∪ B adjacent to u "
            "(purple edge). "
            f"Here: u = {f['u']}, a = {f['a']}, joined by edge {f['e']}. "
            "'Next example' cycles through every (u, witness) pair."),
        lean=("`rintro` = introduce a hypothesis + pattern-match it. The hypothesis "
              "`u ∈ G.nbhdSet (A ∪ B)` unfolds to `∃ a, a ∈ A ∪ B ∧ G.Adj a u`; the pattern "
              "⟨a, haAB, hadj⟩ names its parts: the witness `a`, `haAB : a ∈ A ∪ B` and "
              "`hadj : G.Adj a u`."),
    ),
    dict(
        part="Part 2 · The Lean proof", title="rcases haAB with haA | haB: two cases",
        code="proof", anchors=["rcases haAB with haA | haB", "the witness `a` lies in A or in B"],
        view="RHS", focus="fwd_split",
        math=lambda ex, f: (
            "a ∈ A ∪ B means a ∈ A or a ∈ B, so treat the two cases separately. The purple "
            "edge is now coloured blue (a ∈ A) or orange (a ∈ B). "
            f"Here: a = {f['a']} is in "
            f"{'A' if f['a'] in ex.A else 'B'}{' (and also in B)' if f['a'] in ex.A & ex.B else ''}."),
        lean=("`rcases h with h1 | h2` splits a hypothesis `h : P ∨ Q` into two goals, one "
              "with `h1 : P` and one with `h2 : Q`. Membership in a union, `a ∈ A ∪ B`, unfolds "
              "to `a ∈ A ∨ a ∈ B`, so rcases can split it. Each `·` bullet then proves one "
              "goal."),
    ),
    dict(
        part="Part 2 · The Lean proof", title="Case a ∈ A: exact Or.inl ⟨a, haA, hadj⟩",
        code="proof", anchors=["· -- `a ∈ A`, so `u ∈ N(A)`", "exact Or.inl ⟨a, haA, hadj⟩"],
        view="NA", focus="fwd_A",
        math=lambda ex, f: (
            "The same witness a ∈ A and the same edge show that u ∈ N(A), so u is in "
            "N(A) ∪ N(B). "
            f"Here: {f['a']} ∈ A and edge {f['e']} gives {f['u']} ∈ N(A)."),
        lean=("The goal `u ∈ N(A) ∪ N(B)` unfolds to `u ∈ N(A) ∨ u ∈ N(B)`. `Or.inl` proves "
              "an 'or' from its LEFT part. The anonymous constructor ⟨a, haA, hadj⟩ builds "
              "`∃ a, a ∈ A ∧ G.Adj a u`: first the witness, then the two facts. `exact` closes "
              "the goal with this term."),
    ),
    dict(
        part="Part 2 · The Lean proof", title="Case a ∈ B: exact Or.inr ⟨a, haB, hadj⟩",
        code="proof", anchors=["· -- `a ∈ B`, so `u ∈ N(B)`", "exact Or.inr ⟨a, haB, hadj⟩"],
        view="NB", focus="fwd_B",
        math=lambda ex, f: (
            "This time the witness lies in B, so the same witness and edge show u ∈ N(B), "
            "which is again inside N(A) ∪ N(B). "
            f"Here: {f['a']} ∈ B and edge {f['e']} gives {f['u']} ∈ N(B)."),
        lean=("`Or.inr` proves an 'or' from its RIGHT part, `u ∈ N(B)`. The term inside is "
              "built the same way as before. Both cases are now proved, so `forward` "
              "is done."),
    ),
    dict(
        part="Part 2 · The Lean proof",
        title="have backward + rintro (⟨a, haA, hadj⟩ | ⟨b, hbB, hadj⟩)", code="proof",
        anchors=["have backward", "(⊇) a vertex adjacent",
                 "rintro (⟨a, haA, hadj⟩ | ⟨b, hbB, hadj⟩)"],
        view="RHS", focus="bwd",
        math=lambda ex, f: (
            "Second direction (⊇): assume u ∈ N(A) ∪ N(B). Then u ∈ N(A), with a witness "
            "a ∈ A, or u ∈ N(B), with a witness b ∈ B. "
            f"Here: u = {f['u']} with witness {f['a']} via {f['e']}."),
        lean=("A single rintro does two jobs. `|` splits the 'or' into two goals, and each "
              "⟨…⟩ unpacks the existential inside that case. The two cases are proved by "
              "the next two bullets."),
    ),
    dict(
        part="Part 2 · The Lean proof", title="Case u ∈ N(A): exact ⟨a, Or.inl haA, hadj⟩",
        code="proof", anchors=["a witness in A is also", "exact ⟨a, Or.inl haA, hadj⟩"],
        view="LHS", focus="bwd_A",
        math=lambda ex, f: (
            "A witness a ∈ A also lies in A ∪ B, and the same edge still joins it to u, so "
            "u ∈ N(A ∪ B). "
            f"Here: {f['a']} ∈ A ⊆ A ∪ B and edge {f['e']} gives {f['u']} ∈ N(A ∪ B)."),
        lean=("The goal `u ∈ N(A ∪ B)` unfolds to `∃ a, a ∈ A ∪ B ∧ G.Adj a u`. We give "
              "the witness `a`. Then `Or.inl haA` proves `a ∈ A ∪ B`, which unfolds to "
              "`a ∈ A ∨ a ∈ B`, and `hadj` is reused unchanged."),
    ),
    dict(
        part="Part 2 · The Lean proof", title="Case u ∈ N(B): exact ⟨b, Or.inr hbB, hadj⟩",
        code="proof", anchors=["a witness in B is also", "exact ⟨b, Or.inr hbB, hadj⟩"],
        view="LHS", focus="bwd_B",
        math=lambda ex, f: (
            "Same idea for a witness b ∈ B: b ∈ A ∪ B, with the same edge, so u ∈ N(A ∪ B). "
            f"Here: {f['a']} ∈ B ⊆ A ∪ B and edge {f['e']} gives {f['u']} ∈ N(A ∪ B)."),
        lean=("`Or.inr hbB` proves `b ∈ A ∪ B` from its right part `b ∈ B`. This finishes "
              "`backward`."),
    ),
    dict(
        part="Part 2 · The Lean proof", title="exact ⟨forward, backward⟩: done ∎",
        code="proof", anchors=["combine both inclusions", "exact ⟨forward, backward⟩"],
        view="RHS", focus="ext",
        math=lambda ex, f: (
            "Both inclusions together give 'u ∈ N(A ∪ B) if and only if u ∈ N(A) ∪ N(B)' for "
            "the arbitrary u, so the two sets are equal. "
            f"(Example u = {f['u']}: left {_yn(f['u'] in ex.lhs)}, right "
            f"{_yn(f['u'] in ex.rhs)}.)"),
        lean=("An `↔` is a pair of implications. The anonymous constructor ⟨forward, "
              "backward⟩ packs the two into a proof of the `↔`, and `exact` closes the last "
              "goal. Lean's kernel then re-checks the complete proof."),
    ),
    dict(
        part="Part 3 · Example vs. proof", title="A picture checks examples; Lean proves it",
        code="proof", anchors=[], view="RHS", focus=None,
        math=lambda ex, f: (
            "This window checks ONE graph and the A and B you chose. The script also checks all "
            f"2^9 × 2^9 = {ex.n_pairs:,} pairs (A, B) for this one graph. That is evidence, "
            "not a proof. No other graph is examined: larger or infinite ones, or ones with "
            "other loops and multiple edges. Checking more examples could never cover them "
            "all."),
        lean=("The Lean proof never looks at a particular graph. Each step only unfolds the "
              "definitions of nbhdSet, ∪ and ∃, so the proof holds for every V, E, G, A and "
              "B. `#print axioms GraphCh10.supp09a` reports only Lean's standard axioms "
              "propext and Quot.sound: no sorry and no project axioms."),
    ),
]

VIEWS = ["none", "NA", "NB", "LHS", "RHS"]
VIEW_LABELS = ["nothing", "N(A)", "N(B)", "N(A ∪ B)   left side", "N(A) ∪ N(B)   right side"]


# ---------------------------------------------------------------------------
# 8. The interactive explorer
# ---------------------------------------------------------------------------

class Explorer:
    """Interactive companion: choose A and B by clicking; step through the proof."""

    def __init__(self, n_pairs: int):
        self.n_pairs = n_pairs
        self.lean = read_lean_sources()
        self._check_anchors()
        self.A: frozenset[str] = A
        self.B: frozenset[str] = B
        self.step = 0
        self.example_idx = 0
        self.view = "none"
        self._syncing = False

        for key in ("keymap.back", "keymap.forward"):  # free ← / → for the walkthrough
            plt.rcParams[key] = [k for k in plt.rcParams[key] if k not in ("left", "right")]

        self.fig = plt.figure(figsize=(18, 11.5), facecolor="white")
        try:
            self.fig.canvas.manager.set_window_title("Supp. 9(a): N(A ∪ B) = N(A) ∪ N(B)")
        except AttributeError:
            pass
        self.fig.text(0.015, 0.972, "Supplementary Exercise 9(a):  N(A ∪ B) = N(A) ∪ N(B)",
                      fontsize=18, fontweight="bold", color=COLOR_TEXT, va="center")
        self.fig.text(0.015, 0.94,
                      "An interactive companion to the Lean proof GraphCh10.supp09a. The graph "
                      "is ONE example; the Lean theorem proves the identity for EVERY "
                      "undirected graph and all A, B.",
                      fontsize=10.5, color=COLOR_WARN, style="italic", va="center")

        self.ax_graph = self.fig.add_axes([0.015, 0.36, 0.465, 0.475])
        self.caption = self.fig.text(0.2475, 0.872, "", ha="center", va="top", fontsize=10.5,
                                     color=COLOR_TEXT, linespacing=1.5)
        self.ax_legend = self.fig.add_axes([0.015, 0.29, 0.465, 0.07])
        self.ax_radio = self.fig.add_axes([0.015, 0.03, 0.165, 0.245])
        self.ax_sets = self.fig.add_axes([0.19, 0.03, 0.29, 0.245])
        self.ax_text = self.fig.add_axes([0.505, 0.555, 0.48, 0.365])
        self.ax_code = self.fig.add_axes([0.505, 0.115, 0.48, 0.425])
        for ax in (self.ax_legend, self.ax_sets, self.ax_text, self.ax_code):
            ax.axis("off")
        self.fig.text(0.015, 0.905,
                      "Click a vertex to change it:  none → A → B → both → none.   "
                      "Gold marks what the current step is about.",
                      fontsize=9.8, color="#444444", va="center")

        self.ax_radio.set_title("Highlight on the graph", fontsize=10.5, fontweight="bold",
                                loc="left")
        self.radio = RadioButtons(self.ax_radio, VIEW_LABELS, active=0,
                                  activecolor=COLOR_MEMBER)
        for t in self.radio.labels:
            t.set_fontsize(10)
        self.radio.on_clicked(self._on_view)

        def button(rect, label, cb, color="#F0F0F0"):
            b = Button(self.fig.add_axes(rect), label, color=color, hovercolor="#DDE8F5")
            b.label.set_fontsize(10.5)
            b.on_clicked(cb)
            return b

        self.btn_prev = button([0.505, 0.035, 0.085, 0.055], "◀ Previous", lambda _e: self.go(-1))
        self.btn_next = button([0.700, 0.035, 0.085, 0.055], "Next ▶", lambda _e: self.go(+1),
                               color="#E3EEDF")
        self.btn_example = button([0.795, 0.035, 0.09, 0.055], "Next example",
                                  lambda _e: self.next_example())
        self.btn_reset = button([0.895, 0.035, 0.042, 0.055], "Reset", lambda _e: self.reset())
        self.btn_clear = button([0.943, 0.035, 0.042, 0.055], "Clear", lambda _e: self.clear())
        self.step_label = self.fig.text(0.6425, 0.0625, "", ha="center", va="center",
                                        fontsize=11, fontweight="bold", color=COLOR_TEXT)
        self.fig.text(0.94, 0.1, "Reset / Clear A and B", ha="center", fontsize=8,
                      color="#666666")

        self._draw_legend()
        self.fig.canvas.mpl_connect("button_press_event", self._on_click)
        self.fig.canvas.mpl_connect("key_press_event", self._on_key)
        self.enter_step(0)

    # -- state --------------------------------------------------------------

    def _check_anchors(self) -> None:
        """Every walkthrough anchor must match exactly one line of the real Lean source."""
        for s in STEPS:
            lines = self.lean[s["code"]]
            for anchor in s["anchors"]:
                n = sum(anchor in ln for ln in lines)
                assert n == 1, f"anchor {anchor!r} matches {n} lines of the {s['code']} source"

    @property
    def lhs(self) -> frozenset[str]:
        return nbhd_set(self.A | self.B)

    @property
    def rhs(self) -> frozenset[str]:
        return nbhd_set(self.A) | nbhd_set(self.B)

    def toggle(self, v: str) -> None:
        """none → A → B → both → none."""
        inA, inB = v in self.A, v in self.B
        nxt = {(False, False): (True, False), (True, False): (False, True),
               (False, True): (True, True), (True, True): (False, False)}[(inA, inB)]
        self.A = self.A | {v} if nxt[0] else self.A - {v}
        self.B = self.B | {v} if nxt[1] else self.B - {v}
        self.redraw()

    def reset(self) -> None:
        self.A, self.B = A, B
        self.redraw()

    def clear(self) -> None:
        self.A, self.B = frozenset(), frozenset()
        self.redraw()

    def go(self, delta: int) -> None:
        self.enter_step(max(0, min(len(STEPS) - 1, self.step + delta)))

    def next_example(self) -> None:
        self.example_idx += 1
        self.redraw()

    def enter_step(self, k: int) -> None:
        self.step, self.example_idx = k, 0
        if STEPS[k]["view"] is not None:
            self.set_view(STEPS[k]["view"])
        self.redraw()

    def set_view(self, view: str) -> None:
        self.view = view
        self._syncing = True  # set_active fires on_clicked; do not redraw twice
        self.radio.set_active(VIEWS.index(view))
        self._syncing = False

    # -- events -------------------------------------------------------------

    def _on_view(self, label: str) -> None:
        self.view = VIEWS[VIEW_LABELS.index(label)]
        if not self._syncing:
            self.redraw()

    def _on_click(self, event) -> None:
        if event.inaxes is not self.ax_graph or event.button != 1 or event.xdata is None:
            return
        v = min(V, key=lambda w: (POS[w][0] - event.xdata) ** 2 + (POS[w][1] - event.ydata) ** 2)
        if (POS[v][0] - event.xdata) ** 2 + (POS[v][1] - event.ydata) ** 2 <= (1.4 * NODE_R) ** 2:
            self.toggle(v)

    def _on_key(self, event) -> None:
        if event.key == "right":
            self.go(+1)
        elif event.key == "left":
            self.go(-1)

    # -- what to highlight --------------------------------------------------

    def view_info(self) -> tuple[frozenset[str], dict[str, str], str]:
        """(green-ringed set, witness-edge colours, caption) for the selected view."""
        SA, SB = self.A, self.B
        na, nb = nbhd_set(SA), nbhd_set(SB)
        by_set = lambda a: COLOR_A if a in SA else COLOR_B  # noqa: E731
        if self.view == "NA":
            return na, witness_edges(SA, na, lambda a: COLOR_A), \
                f"N(A) = {fmt(na)}   (blue edges: a witness a ∈ A)"
        if self.view == "NB":
            return nb, witness_edges(SB, nb, lambda a: COLOR_B), \
                f"N(B) = {fmt(nb)}   (orange edges: a witness b ∈ B)"
        if self.view == "LHS":
            return self.lhs, witness_edges(SA | SB, self.lhs, lambda a: COLOR_AB), \
                f"Left side  N(A ∪ B) = {fmt(self.lhs)}   (purple edges: a witness in A ∪ B)"
        if self.view == "RHS":
            return self.rhs, witness_edges(SA | SB, self.rhs, by_set), \
                f"Right side  N(A) ∪ N(B) = {fmt(self.rhs)}   (edge colour: witness in A or B)"
        return frozenset(), {}, "The graph G"

    def focus_info(self, kind: str | None) -> tuple[dict | None, int]:
        """What the current step highlights in gold / bold. Returns (info, #examples)."""
        if kind is None:
            return None, 0
        SA, SB = self.A, self.B
        if kind == "loop_multi":
            return dict(tags={}, edges={e: COLOR_FOCUS for e in ("e10", "e7", "e8")},
                        caption="gold: the loop e10 = {d} and the multiple edges e7, e8 = {d, h}"
                        ), 1
        if kind in ("vertex_nbrs", "ext"):
            k = self.example_idx % len(V)
            v = V[k]
            if kind == "vertex_nbrs":
                inc = {e: COLOR_FOCUS for e in E if v in ends[e]}
                return dict(v=v, tags={v: "v"}, edges=inc, ring=nbhd(v),
                            caption=f"v = {v}: its edges in gold, its neighbors N({v}) = "
                                    f"{fmt(nbhd(v))} ringed green"), len(V)
            return dict(u=v, tags={v: "u"}, edges={},
                        caption=f"u = {v}:  u ∈ N(A ∪ B)? {_yn(v in self.lhs)}    "
                                f"u ∈ N(A) ∪ N(B)? {_yn(v in self.rhs)}"), len(V)

        union = SA | SB
        if kind in ("fwd", "fwd_split", "fwd_A", "fwd_B"):
            cands = [(u, a, e) for u in sorted(self.lhs) for a, e in witnesses(union, u)]
            if kind == "fwd_A":
                cands = [c for c in cands if c[1] in SA]
            if kind == "fwd_B":
                cands = [c for c in cands if c[1] in SB]
        elif kind in ("bwd", "bwd_A", "bwd_B"):
            ca = [(u, a, e) for u in sorted(nbhd_set(SA)) for a, e in witnesses(SA, u)]
            cb = [(u, a, e) for u in sorted(nbhd_set(SB)) for a, e in witnesses(SB, u)]
            cands = {"bwd": ca + cb, "bwd_A": ca, "bwd_B": cb}[kind]
        else:
            raise ValueError(kind)
        if not cands:
            return None, 0
        u, a, e = cands[self.example_idx % len(cands)]
        if kind == "fwd":
            color = COLOR_AB
        elif kind in ("fwd_A", "bwd_A"):
            color = COLOR_A
        elif kind in ("fwd_B", "bwd_B"):
            color = COLOR_B
        elif kind == "bwd":
            color = COLOR_A if (u, a, e) in ca else COLOR_B
        else:  # fwd_split: colour by the case the witness falls into
            color = COLOR_A if a in SA else COLOR_B
        tags = {u: "u"} if u != a else {u: "u = a"}
        if u != a:
            tags[a] = "a"
        n = len(cands)
        return dict(u=u, a=a, e=e, tags=tags, edges={e: color},
                    caption=f"u = {u},  witness a = {a},  edge {e} = "
                            f"{fmt(ends[e])}   (example {self.example_idx % n + 1} of {n})"), n

    # -- drawing ------------------------------------------------------------

    def redraw(self) -> None:
        lhs, rhs = check_identity(self.A, self.B)  # live assertion for the chosen A, B
        s = STEPS[self.step]
        focus, n_examples = self.focus_info(s["focus"])
        self._draw_graph(focus)
        self._draw_sets(lhs, rhs, focus)
        self._draw_text(s, focus)
        self._draw_code(s)
        self.step_label.set_text(f"Step {self.step + 1} / {len(STEPS)}")
        self.btn_example.ax.set_visible(n_examples > 1)
        self.fig.canvas.draw_idle()

    def _draw_graph(self, focus: dict | None) -> None:
        ax = self.ax_graph
        ax.clear()
        ring, edge_colors, caption = self.view_info()
        emphasized: frozenset[str] = frozenset()
        tags: dict[str, str] = {}
        if focus is not None:
            edge_colors = {**edge_colors, **focus["edges"]}
            emphasized = frozenset(focus["edges"]) if "e" in focus else frozenset()
            tags = focus["tags"]
            if "ring" in focus:
                ring = focus["ring"]
            caption = caption + "\n" + focus["caption"]
        draw_edges(ax, edge_colors, emphasized, shrink=16)

        for v in V:
            x, y = POS[v]
            if v in tags:  # gold halo for the vertex the step is about
                ax.add_patch(Circle((x, y), NODE_R + 0.15, facecolor=COLOR_FOCUS, alpha=0.55,
                                    edgecolor="none", zorder=3.5))
            inA, inB = v in self.A, v in self.B
            if inA and inB:  # both: half blue, half orange
                ax.add_patch(Wedge((x, y), NODE_R, 90, 270, facecolor=COLOR_A, zorder=4))
                ax.add_patch(Wedge((x, y), NODE_R, 270, 90, facecolor=COLOR_B, zorder=4))
            else:
                ax.add_patch(Circle((x, y), NODE_R, facecolor=fill_color(v, self.A, self.B),
                                    zorder=4))
            member = v in ring
            ax.add_patch(Circle((x, y), NODE_R, fill=False, zorder=4.5,
                                edgecolor=COLOR_MEMBER if member else "#8C8C8C",
                                linewidth=4 if member else 1))
            ax.text(x, y, v, ha="center", va="center", fontsize=13, fontweight="bold",
                    color="white" if (inA or inB) else COLOR_TEXT, zorder=5)
            if v in tags:
                ax.text(x - 0.34, y + 0.34, tags[v], ha="right", va="bottom", fontsize=10.5,
                        fontweight="bold", color="#5A4500", zorder=6,
                        bbox=dict(boxstyle="round,pad=0.2", fc="#FFF4C2", ec=COLOR_FOCUS))

        self.caption.set_text(caption)
        ax.set_xlim(-0.75, 5.45)
        ax.set_ylim(-0.55, 4.05)
        ax.set_aspect("equal")
        ax.axis("off")

    def _draw_legend(self) -> None:
        handles = [
            Patch(facecolor=COLOR_A, edgecolor="#8C8C8C", label="vertex in A"),
            Patch(facecolor=COLOR_B, edgecolor="#8C8C8C", label="vertex in B"),
            Patch(facecolor=COLOR_OTHER, edgecolor="#8C8C8C", label="in neither"),
            Line2D([], [], marker="o", color="none", markerfacecolor="white",
                   markeredgecolor=COLOR_MEMBER, markeredgewidth=3, markersize=12,
                   label="green ring: in the highlighted set"),
            Line2D([], [], color=COLOR_A, linewidth=3.5, label="witness in A"),
            Line2D([], [], color=COLOR_B, linewidth=3.5, label="witness in B"),
            Line2D([], [], color=COLOR_AB, linewidth=3.5, label="witness in A ∪ B"),
            Line2D([], [], marker="o", color="none", markerfacecolor=COLOR_FOCUS, alpha=0.7,
                   markersize=14, label="gold: what this step is about"),
        ]
        self.ax_legend.legend(handles=handles, loc="center", ncol=4, frameon=False,
                              fontsize=9.5, handlelength=2.2, columnspacing=1.4)
        self.ax_legend.text(0.5, -0.05, "A vertex in both A and B is drawn half blue, "
                            "half orange.", transform=self.ax_legend.transAxes, ha="center",
                            fontsize=8.8, color="#666666")

    def _draw_sets(self, lhs, rhs, focus) -> None:
        ax = self.ax_sets
        ax.clear()
        ax.axis("off")
        ax.add_patch(plt.Rectangle((0, 0), 1, 1, transform=ax.transAxes, facecolor="#F7F7F7",
                                   edgecolor="#D0D0D0"))
        rows = [
            ("A", fmt(self.A), COLOR_A), ("B", fmt(self.B), COLOR_B),
            ("N(A)", fmt(nbhd_set(self.A)), COLOR_TEXT), ("N(B)", fmt(nbhd_set(self.B)), COLOR_TEXT),
            ("left:  N(A ∪ B)", fmt(lhs), COLOR_TEXT), ("right: N(A) ∪ N(B)", fmt(rhs), COLOR_TEXT),
        ]
        ax.text(0.04, 0.93, "Computed live from the edges", transform=ax.transAxes,
                fontsize=10.5, fontweight="bold", va="top")
        for i, (name, val, col) in enumerate(rows):
            y = 0.79 - i * 0.105
            ax.text(0.04, y, name, transform=ax.transAxes, fontsize=10, va="top", color=col,
                    fontweight="bold")
            ax.text(0.47, y, "= " + val, transform=ax.transAxes, fontsize=10, va="top",
                    family="DejaVu Sans Mono")
        equal = lhs == rhs
        ax.text(0.04, 0.12, ("✓ the two sides are equal for this A and B" if equal
                             else "✗ the two sides differ"),
                transform=ax.transAxes, fontsize=10.5, fontweight="bold", va="top",
                color=COLOR_MEMBER if equal else COLOR_WARN)

    def _draw_text(self, s: dict, focus: dict | None) -> None:
        ax = self.ax_text
        ax.clear()
        ax.axis("off")
        math = s["math"]
        needs_focus = s["focus"] not in (None, "loop_multi")
        if callable(math):
            math = NO_CASE if (needs_focus and focus is None) else math(self, focus)
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
                    fontweight="bold", color=COLOR_MEMBER if head == "In Lean" else COLOR_A)
            y -= 1.25 * line
            ax.text(0, y, "\n".join(lines), transform=ax.transAxes, fontsize=size, va="top",
                    color=COLOR_TEXT, linespacing=1.42)
            y -= (len(lines) + 0.6) * line

    def _draw_code(self, s: dict) -> None:
        ax = self.ax_code
        ax.clear()
        ax.axis("off")
        ax.add_patch(plt.Rectangle((0, 0), 1, 1, transform=ax.transAxes,
                                   facecolor=COLOR_CODE_BG, edgecolor="#D0D0D0"))
        src = self.lean[s["code"]]
        name = ("GraphCh10/Exercises/Supp09a.lean" if s["code"] == "proof"
                else "GraphCh10/Definitions.lean")
        ax.text(0.015, 0.975, f"Lean source: {name}  (read from disk; highlighted = this step)",
                transform=ax.transAxes, fontsize=9.5, fontweight="bold", va="top",
                color="#555555")
        n = max(len(src), 22)
        step_y = 0.9 / n
        for i, ln in enumerate(src):
            hl = any(a in ln for a in s["anchors"])
            y = 0.915 - i * step_y
            if hl:
                ax.add_patch(plt.Rectangle((0.008, y - step_y * 0.92), 0.984, step_y * 0.98,
                                           transform=ax.transAxes, facecolor=COLOR_CODE_HL,
                                           edgecolor=COLOR_FOCUS, linewidth=1))
            ax.text(0.015, y, ln if ln else " ", transform=ax.transAxes, va="top",
                    fontsize=9, family="DejaVu Sans Mono",
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


def self_test(ex: Explorer, outdir: Path) -> None:
    outdir.mkdir(parents=True, exist_ok=True)
    # 1. Every step renders, for every example the step offers.
    for k in range(len(STEPS)):
        ex.enter_step(k)
        _f, n = ex.focus_info(STEPS[k]["focus"])
        for _ in range(max(n, 1)):
            ex.redraw()
            ex.next_example()
        ex.enter_step(k)
        ex.fig.savefig(outdir / f"step_{k + 1:02d}.png", dpi=90)
    # 2. Simulated clicks on the Next / Previous buttons move the walkthrough.
    ex.enter_step(0)
    _press(ex.fig, ex.btn_next.ax, 0.5, 0.5, data=False)
    assert ex.step == 1, "Next button did not advance"
    _press(ex.fig, ex.btn_prev.ax, 0.5, 0.5, data=False)
    assert ex.step == 0, "Previous button did not go back"
    # 3. Simulated clicks on vertices cycle membership none → A → B → both → none.
    ex.enter_step(3)
    seen = []
    for _ in range(4):
        _press(ex.fig, ex.ax_graph, *POS["i"])
        seen.append(("i" in ex.A, "i" in ex.B))
    assert seen == [(True, False), (False, True), (True, True), (False, False)], seen
    _press(ex.fig, ex.ax_graph, *POS["i"])  # i ∈ A now: e joins i, so e ∈ N(A)
    assert "e" in nbhd_set(ex.A) and ex.lhs == ex.rhs
    _press(ex.fig, ex.ax_graph, *POS["c"])  # c: B → both
    assert "c" in ex.A and "c" in ex.B
    ex.fig.savefig(outdir / "custom_AB.png", dpi=90)
    # 4. Radio buttons change the view; Clear empties A and B; empty cases render.
    ex.set_view("LHS")
    _press(ex.fig, ex.btn_clear.ax, 0.5, 0.5, data=False)
    assert ex.A == ex.B == frozenset() and ex.lhs == ex.rhs == frozenset()
    for k in range(len(STEPS)):
        ex.enter_step(k)
    ex.enter_step(9)
    ex.fig.savefig(outdir / "empty_case.png", dpi=90)
    _press(ex.fig, ex.btn_reset.ax, 0.5, 0.5, data=False)
    assert (ex.A, ex.B) == (A, B)
    print(f"Explorer self-test passed: {len(STEPS)} steps rendered, buttons and clicks "
          f"work; snapshots in {outdir}")


# ---------------------------------------------------------------------------
# 10. Entry point
# ---------------------------------------------------------------------------

def main() -> None:
    try:
        sys.stdout.reconfigure(encoding="utf-8")  # so ∪, ∈ print on Windows consoles
    except (AttributeError, ValueError):
        pass
    parser = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    parser.add_argument("--static", action="store_true",
                        help="only run the checks and save the PNG (no window)")
    parser.add_argument("--snapshots", metavar="DIR", type=Path,
                        help="headless self-test of the explorer; save one PNG per step")
    args = parser.parse_args()

    n_pairs = run_checks()
    print("Graph: V =", fmt(V), f"with {len(E)} edges (including a loop and a multiple edge)")
    print("A =", fmt(A), "  B =", fmt(B))
    print("N(A)         =", fmt(N_A))
    print("N(B)         =", fmt(N_B))
    print("N(A ∪ B)     =", fmt(LHS))
    print("N(A) ∪ N(B)  =", fmt(RHS))
    print(f"All assertions passed (identity, both inclusions, {n_pairs:,} subset pairs).")

    out = Path(__file__).resolve().parent / "supp09a.png"
    fig = build_figure(n_pairs)
    fig.savefig(out, dpi=150, facecolor="white")
    plt.close(fig)
    print("Saved", out)

    if args.snapshots:
        self_test(Explorer(n_pairs), args.snapshots)
    elif not args.static:
        if matplotlib.get_backend().lower() == "agg":
            print("No interactive Matplotlib backend is available; the explorer needs a "
                  "window (e.g. TkAgg). The PNG has been saved.")
            return
        Explorer(n_pairs)
        print("Opening the interactive explorer (close the window to exit).")
        plt.show()


if __name__ == "__main__":
    main()
