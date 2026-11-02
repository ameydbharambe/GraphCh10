"""Visualization for Rosen Ch. 10, Supplementary Exercise 28:  isomorphism does not respect union.

    "Suppose that G₁ and H₁ are isomorphic and that G₂ and H₂ are isomorphic. Prove or
     disprove that G₁ ∪ G₂ and H₁ ∪ H₂ are isomorphic."

Answer: DISPROVED. An EDUCATIONAL COMPANION to the Lean theorem `GraphCh10.supp28`
(GraphCh10/Exercises/Supp28.lean), for students learning Lean 4 and introductory graph
theory. It has two parts:

1. A static summary figure (visualizations/supp28.png).
2. An interactive explorer: see the four graphs G₁, G₂, H₁, H₂ of the counterexample and
   the two unions; relabel H₂ (any copy of K₂ inside {0, 1, 2, 3}) and watch the union
   H₁ ∪ H₂ change while G₂ ≅ H₂ keeps holding; try maps f from the vertices of G₁ ∪ G₂ to
   the vertices of H₁ ∪ H₂ and see why no bijection exists (2 arrows cannot hit 4
   targets); and step through the actual Lean proof with Previous/Next. Each step explains
   the mathematics and the Lean tactics and highlights the matching parts of the picture.
   The Lean code shown is read from the project files at runtime.

The key picture: a union is formed LABEL BY LABEL, so it depends on how the two graphs
overlap (which vertex names they share). An isomorphism only renames vertices, so it
forgets the names, and with them the overlap. G₁ ∪ G₂ is two copies of K₂ stacked on the
same labels (2 vertices); H₁ ∪ H₂ is two copies of K₂ side by side (4 vertices).

Unlike a "for every" theorem, the Lean theorem is a NEGATION `¬ ∀ …`: one counterexample
disproves the claim. The pictures illustrate that counterexample; the facts about it
(the hypotheses hold, the unions have 2 and 4 vertices, 2 ≠ 4) are established by the Lean
proof. The extra searches in this script (all maps, all relabellings of H₂, all simple
graphs inside a 3-element set) are illustrations, not part of the proof.

The graph model follows GraphCh10/Definitions.lean exactly:

* `SetSimpleGraph α` -- `V : Set α` and `E : Set (Sym2 α)`; here a graph is the pair
  (V, E) with V a frozenset of labels and E a frozenset of 2-element frozensets {u, w}
  (`s(u, w)`). `edge_sub`: ends of edges are in V; `loopless`: no edge s(v, v).
* `G₁ ∪ G₂ := (G₁.V ∪ G₂.V, G₁.E ∪ G₂.E)`.
* `Isomorphic G₁ G₂ := ∃ f : G₁.V ≃ G₂.V, ∀ v₁ v₂, s(f v₁, f v₂) ∈ G₂.E ↔ s(v₁, v₂) ∈ G₁.E`.
* `k2Low`, `k2High` and the instance `hall (Fin 4) (Fin 4) k2Low k2Low k2Low k2High` are
  parsed from Supp28.lean, so the pictures show exactly the graphs the Lean proof uses.

Every vertex set, union and isomorphism check is COMPUTED from these definitions.

Run (from the project root):
    python -m pip install networkx matplotlib
    python visualizations/supp28.py              # save the PNG, then open the explorer
    python visualizations/supp28.py --static     # only checks + PNG (no window)
    python visualizations/supp28.py --snapshots DIR
        # headless self-test: drives the explorer through every walkthrough step,
        # simulates button presses and keys, and saves PNGs into DIR

Explorer controls:
    Relabel H₂: {a, b}      make H₂ the copy of K₂ on the labels a, b (G₂ ≅ H₂ still holds)
    Reset                   back to the Lean counterexample (H₂ on {2, 3}) and the first map
    f(0) ▸ / f(1) ▸         change where the map f sends a vertex of G₁ ∪ G₂
    Next map ▸              go through ALL maps V(G₁ ∪ G₂) → V(H₁ ∪ H₂) one by one
    ◀ Previous / Next ▶     move through the walkthrough (also ← / → keys)
    Next example            show another pair (v₁, v₂) for the steps that check edges
"""

from __future__ import annotations

import argparse
import re
import sys
import textwrap
from collections import namedtuple
from itertools import combinations, permutations, product
from pathlib import Path

import matplotlib

# Pick a file-only backend before pyplot is imported when no window will be opened.
if "--static" in sys.argv or "--snapshots" in sys.argv:
    matplotlib.use("Agg")

import matplotlib.patheffects as pe
import matplotlib.pyplot as plt
import networkx as nx
from matplotlib.backend_bases import KeyEvent, MouseEvent
from matplotlib.gridspec import GridSpec, GridSpecFromSubplotSpec
from matplotlib.lines import Line2D
from matplotlib.patches import Circle, ConnectionPatch, FancyBboxPatch, Patch, Wedge
from matplotlib.widgets import Button

PROJECT_ROOT = Path(__file__).resolve().parent.parent
PROOF_FILE = PROJECT_ROOT / "GraphCh10" / "Exercises" / "Supp28.lean"
DEFS_FILE = PROJECT_ROOT / "GraphCh10" / "Definitions.lean"

# The theorem statement approved by the project owner (checked against the Lean file).
APPROVED_STATEMENT = [
    "theorem supp28 :",
    "    ¬ ∀ (α β : Type)",
    "        (G₁ G₂ : SetSimpleGraph α)",
    "        (H₁ H₂ : SetSimpleGraph β),",
    "        G₁.Isomorphic H₁ →",
    "        G₂.Isomorphic H₂ →",
    "        (G₁ ∪ G₂).Isomorphic (H₁ ∪ H₂) := by",
]

SG = namedtuple("SG", "V E")  # a SetSimpleGraph: V a frozenset, E a frozenset of frozensets


def _require(path: Path) -> list[str]:
    if not path.exists():
        sys.exit(f"error: cannot find {path}; run this script inside the GraphCh10 project")
    return path.read_text(encoding="utf-8").splitlines()


# ---------------------------------------------------------------------------
# 1. The definitions, mirroring GraphCh10/Definitions.lean
# ---------------------------------------------------------------------------

def s_(u: int, w: int) -> frozenset:
    """`s(u, w)`: the unordered pair {u, w} (a 1-element set when u = w, i.e. a loop)."""
    return frozenset((u, w))


def is_set_simple_graph(G: SG) -> bool:
    """The two proof fields of `SetSimpleGraph`: `edge_sub` and `loopless`."""
    edge_sub = all(x in G.V for p in G.E for x in p)
    loopless = all(len(p) == 2 for p in G.E)  # `¬ p.IsDiag`: p is not s(v, v)
    return edge_sub and loopless


def union(G1: SG, G2: SG) -> SG:
    """`G₁ ∪ G₂ := (G₁.V ∪ G₂.V, G₁.E ∪ G₂.E)`."""
    return SG(G1.V | G2.V, G1.E | G2.E)


def is_bijection(f: dict, A, B) -> bool:
    """f : A → B is a one-to-one correspondence (`A ≃ B`)."""
    return set(f) == set(A) and set(f.values()) == set(B) and len(set(f.values())) == len(A)


def edge_condition(G: SG, H: SG, f: dict) -> bool:
    """`∀ v₁ v₂ : G.V, s(f v₁, f v₂) ∈ H.E ↔ s(v₁, v₂) ∈ G.E`."""
    return all((s_(f[a], f[b]) in H.E) == (s_(a, b) in G.E) for a in G.V for b in G.V)


def is_isomorphism(G: SG, H: SG, f: dict) -> bool:
    """f witnesses `Isomorphic G H`: a bijection G.V ≃ H.V satisfying the edge condition."""
    return is_bijection(f, G.V, H.V) and edge_condition(G, H, f)


def isomorphisms(G: SG, H: SG):
    """Every isomorphism G → H (brute force over all bijections)."""
    dom = sorted(G.V)
    if len(dom) != len(H.V):
        return
    for img in permutations(sorted(H.V)):
        f = dict(zip(dom, img))
        if edge_condition(G, H, f):
            yield f


def isomorphic(G: SG, H: SG) -> bool:
    """`G.Isomorphic H`."""
    return next(isomorphisms(G, H), None) is not None


def all_maps(A, B):
    """Every function A → B (as dicts), in lexicographic order."""
    dom, cod = sorted(A), sorted(B)
    for img in product(cod, repeat=len(dom)):
        yield dict(zip(dom, img))


def map_counts(G: SG, H: SG) -> dict:
    """How many maps G.V → H.V are one-to-one, onto, bijections, isomorphisms."""
    c = dict(total=0, inj=0, onto=0, bij=0, iso=0)
    for f in all_maps(G.V, H.V):
        c["total"] += 1
        inj = len(set(f.values())) == len(f)
        onto = set(f.values()) == set(H.V)
        c["inj"] += inj
        c["onto"] += onto
        c["bij"] += inj and onto
        c["iso"] += inj and onto and edge_condition(G, H, f)
    return c


def k2(a: int, b: int) -> SG:
    """K₂ on the labels {a, b}: two vertices, one edge."""
    return SG(frozenset((a, b)), frozenset({s_(a, b)}))


def all_simple_graphs(n: int) -> list[SG]:
    """Every SetSimpleGraph inside the ambient set {0, …, n − 1}."""
    out = []
    for k in range(n + 1):
        for V in combinations(range(n), k):
            pairs = [s_(a, b) for a, b in combinations(V, 2)]
            for m in range(len(pairs) + 1):
                for E in combinations(pairs, m):
                    out.append(SG(frozenset(V), frozenset(E)))
    return out


def to_nx(G: SG) -> nx.Graph:
    g = nx.Graph()
    g.add_nodes_from(G.V)
    g.add_edges_from(tuple(p) for p in G.E)
    return g


# ---------------------------------------------------------------------------
# 2. The counterexample, parsed from GraphCh10/Exercises/Supp28.lean
# ---------------------------------------------------------------------------

GRAPH_DEF = re.compile(r"^def (\w+) : SetSimpleGraph \(Fin (\d+)\) where$")
V_LINE = re.compile(r"^\s+V := \{([\d, ]*)\}$")
E_LINE = re.compile(r"^\s+E := \{(.*)\}$")
HALL = re.compile(r"hall \(Fin (\d+)\) \(Fin (\d+)\) (\w+) (\w+) (\w+) (\w+) h₁ h₂")
SHIFT = re.compile(r"toFun := fun x => ⟨x\.1 \+ (\d+),")
UNION_V = re.compile(r"^theorem (union_\w+) : \((\w+) ∪ (\w+)\)\.V = "
                     r"↑\(\{([\d, ]+)\} : Finset \(Fin (\d+)\)\)")


def parse_graphs() -> tuple[dict[str, SG], int]:
    """`def NAME : SetSimpleGraph (Fin n) where  V := {…}  E := {s(a, b), …}`."""
    lines = _require(PROOF_FILE)
    graphs, amb = {}, None
    for i, ln in enumerate(lines):
        m = GRAPH_DEF.match(ln)
        if not m:
            continue
        mv, me = V_LINE.match(lines[i + 1]), E_LINE.match(lines[i + 2])
        assert mv and me, f"`def {m.group(1)}` has an unexpected shape"
        V = frozenset(int(x) for x in mv.group(1).replace(" ", "").split(",") if x)
        E = frozenset(s_(int(a), int(b)) for a, b in re.findall(r"s\((\d+), (\d+)\)",
                                                                 me.group(1)))
        graphs[m.group(1)] = SG(V, E)
        assert amb in (None, int(m.group(2)))
        amb = int(m.group(2))
    assert set(graphs) == {"k2Low", "k2High"}, f"unexpected graph definitions {set(graphs)}"
    return graphs, amb


def parse_instance() -> tuple[int, int, list[str]]:
    """The line `hall (Fin a) (Fin b) G₁ G₂ H₁ H₂ h₁ h₂` of the main proof."""
    text = "\n".join(_require(PROOF_FILE))
    hits = HALL.findall(text)
    assert len(hits) == 1, "expected exactly one application of `hall`"
    a, b, *names = hits[0]
    return int(a), int(b), names


def parse_shift() -> int:
    """The bijection in `k2Low_isomorphic_k2High`: `fun x => ⟨x.1 + k, …⟩`."""
    hits = SHIFT.findall("\n".join(_require(PROOF_FILE)))
    assert len(hits) == 1, "expected exactly one `toFun := fun x => ⟨x.1 + k`"
    return int(hits[0])


def parse_union_lemmas() -> dict[str, tuple[str, str, frozenset]]:
    """`theorem union_… : (A ∪ B).V = ↑({…} : Finset (Fin 4))`: the claimed vertex sets."""
    out = {}
    for ln in _require(PROOF_FILE):
        m = UNION_V.match(ln)
        if m:
            out[m.group(1)] = (m.group(2), m.group(3),
                               frozenset(int(x) for x in m.group(4).replace(" ", "").split(",")))
    assert set(out) == {"union_low_low_V", "union_low_high_V"}, set(out)
    return out


GRAPHS, AMBIENT = parse_graphs()
_A, _B, INSTANCE = parse_instance()
assert _A == _B == AMBIENT, "the counterexample should use α = β = Fin 4"
ROLES = ("G₁", "G₂", "H₁", "H₂")
LEAN_GRAPHS = dict(zip(ROLES, (GRAPHS[n] for n in INSTANCE)))  # role -> graph
LEAN_NAMES = dict(zip(ROLES, INSTANCE))                         # role -> Lean name
SHIFT_K = parse_shift()
UNION_LEMMAS = parse_union_lemmas()
LEAN_H2_PAIR = tuple(sorted(LEAN_GRAPHS["H₂"].V))


def shift_map(G: SG) -> dict:
    """v ↦ v + k in Fin n (addition mod n), restricted to G.V."""
    return {v: (v + SHIFT_K) % AMBIENT for v in sorted(G.V)}


def iso_map(G: SG, H: SG) -> dict | None:
    """The shift map if it is an isomorphism (as in the Lean proof), else the first one found."""
    f = shift_map(G)
    if is_isomorphism(G, H, f):
        return f
    return next(isomorphisms(G, H), None)


def fmt_set(xs) -> str:
    return "{" + ", ".join(map(str, sorted(xs))) + "}" if xs else "∅"


def fmt_edges(E) -> str:
    return "{" + ", ".join(fmt_set(p) for p in sorted(E, key=sorted)) + "}" if E else "∅"


def fmt_map(f: dict) -> str:
    return ", ".join(f"{a}↦{b}" for a, b in sorted(f.items()))


def fmt_graph(G: SG) -> str:
    return f"V = {fmt_set(G.V)},  E = {fmt_edges(G.E)}"


# ---------------------------------------------------------------------------
# 3. Programmatic checks
# ---------------------------------------------------------------------------

def check_statement() -> None:
    """The Lean file still contains exactly the approved theorem statement."""
    lines = _require(PROOF_FILE)
    i = next(i for i, ln in enumerate(lines) if ln.startswith("theorem supp28"))
    assert lines[i:i + len(APPROVED_STATEMENT)] == APPROVED_STATEMENT, \
        "the statement of supp28 has changed"


def run_checks() -> dict:
    """Assert every fact the pictures and the walkthrough rely on. Returns summary numbers."""
    check_statement()
    G1, G2, H1, H2 = (LEAN_GRAPHS[r] for r in ROLES)
    # The parsed graphs are simple graphs, and they are the two copies of K₂ the file describes.
    assert all(is_set_simple_graph(G) for G in GRAPHS.values())
    assert GRAPHS["k2Low"] == k2(0, 1) and GRAPHS["k2High"] == k2(2, 3)
    assert AMBIENT == 4
    # h₁: the identity is an isomorphism G₁ → H₁ (isomorphic_refl).
    assert is_isomorphism(G1, H1, {v: v for v in G1.V})
    # h₂: v ↦ v + 2 is an isomorphism G₂ → H₂ (k2Low_isomorphic_k2High), inverse w ↦ w − 2.
    f = shift_map(G2)
    assert f == {0: 2, 1: 3} and is_isomorphism(G2, H2, f)
    assert all((f[v] - SHIFT_K) % AMBIENT == v for v in G2.V)
    # The two unions and the two vertex-set lemmas.
    UG, UH = union(G1, G2), union(H1, H2)
    assert is_set_simple_graph(UG) and is_set_simple_graph(UH)
    for name, (a, b, vs) in UNION_LEMMAS.items():
        assert union(GRAPHS[a], GRAPHS[b]).V == vs, name
    assert UG.V == UNION_LEMMAS["union_low_low_V"][2] == frozenset({0, 1})
    assert UH.V == UNION_LEMMAS["union_low_high_V"][2] == frozenset({0, 1, 2, 3})
    assert len(UG.E) == 1 and len(UH.E) == 2
    # The conclusion fails: no bijection at all (pigeonhole), so no isomorphism.
    counts = map_counts(UG, UH)
    assert counts == dict(total=16, inj=12, onto=0, bij=0, iso=0), counts
    assert not isomorphic(UG, UH)
    assert not nx.is_isomorphic(to_nx(UG), to_nx(UH))
    # Relabelling H₂: G₂ ≅ H₂ always, but the unions are isomorphic only for H₂ on {0, 1}.
    relabel = {}
    for a, b in combinations(range(AMBIENT), 2):
        h2 = k2(a, b)
        assert isomorphic(G2, h2)
        uh = union(H1, h2)
        iso = isomorphic(UG, uh)
        assert iso == nx.is_isomorphic(to_nx(UG), to_nx(uh))
        assert iso == ((a, b) == (0, 1))
        assert len(uh.V) == 4 - len(h2.V & H1.V)
        relabel[(a, b)] = (len(uh.V), iso)
    # Every simple graph is isomorphic to itself, and isomorphic graphs have equally many
    # vertices (isomorphic_refl, card_eq_of_isomorphic), for all graphs inside {0, 1, 2}.
    gs = all_simple_graphs(3)
    idx = {G: i for i, G in enumerate(gs)}
    assert len(gs) == 18
    iso = [[isomorphic(G, H) for H in gs] for G in gs]
    for i, G in enumerate(gs):
        assert iso[i][i] and is_isomorphism(G, G, {v: v for v in G.V})
        for j, H in enumerate(gs):
            if iso[i][j]:
                assert len(G.V) == len(H.V)
    # How often the claim fails inside {0, 1, 2} (illustration: all 18⁴ quadruples).
    un = [[idx[union(A, B)] for B in gs] for A in gs]
    n_hyp = n_fail = 0
    for i1, i2, j1, j2 in product(range(len(gs)), repeat=4):
        if iso[i1][j1] and iso[i2][j2]:
            n_hyp += 1
            n_fail += not iso[un[i1][i2]][un[j1][j2]]
    assert n_fail > 0
    return dict(counts=counts, relabel=relabel, n_graphs3=len(gs), n_hyp=n_hyp, n_fail=n_fail)


# ---------------------------------------------------------------------------
# 4. Shared drawing helpers
# ---------------------------------------------------------------------------

COLOR_ONE = "#E08A2C"      # orange: comes from the FIRST graph (G₁ or H₁)
COLOR_TWO = "#7B3FB8"      # purple: comes from the SECOND graph (G₂ or H₂)
COLOR_GHOST = "#B5B5B5"    # a label of Fin 4 that is not a vertex of this graph
COLOR_OK = "#1E8C45"       # green: a check that holds
COLOR_FOCUS = "#F2B705"    # gold: what the current walkthrough step is about
COLOR_TEXT = "#222222"
COLOR_WARN = "#B03030"
COLOR_VERTEX = "#3B6FB6"
COLOR_CODE_BG = "#FBFBF8"
COLOR_CODE_HL = "#FFF1B8"
COLOR_PANEL = "#F7F7F7"

# Fixed positions of the four labels 0, 1, 2, 3 of Fin 4, the same in every small picture.
POS = {0: (-1.0, 0.7), 1: (-1.0, -0.7), 2: (1.0, 0.7), 3: (1.0, -0.7)}
NODE_R = 0.3
XLIM, YLIM = (-1.85, 1.85), (-1.3, 1.3)


def draw_sg(ax, G: SG, color: str = COLOR_ONE, parts: list | None = None,
            tags: dict | None = None, edge_hl: set | None = None, fontsize: float = 12,
            ghosts: bool = True) -> None:
    """Draw a SetSimpleGraph inside Fin 4. `parts` = [(graph, colour), …] colours each vertex
    and edge by the graph(s) it comes from (half-and-half when from both); labels of Fin 4
    that are not vertices are faint dashed circles; `tags` adds a gold halo and a label;
    `edge_hl` edges get a gold outline."""
    parts = parts or [(G, color)]
    tags = tags or {}
    edge_hl = edge_hl or set()
    for p in sorted(G.E, key=sorted):
        u, w = sorted(p)
        (x1, y1), (x2, y2) = POS[u], POS[w]
        cols = [c for P, c in parts if p in P.E] or [COLOR_TEXT]
        effects = [pe.Stroke(linewidth=11, foreground=COLOR_FOCUS), pe.Normal()] \
            if p in edge_hl else None
        ln, = ax.plot([x1, x2], [y1, y2], color=cols[0], linewidth=4, zorder=2,
                      solid_capstyle="round")
        if effects:
            ln.set_path_effects(effects)
        if len(cols) > 1:  # an edge of both graphs: one edge of the union, two colours
            ax.plot([x1, x2], [y1, y2], color=cols[1], linewidth=4, zorder=2.1,
                    linestyle=(0, (3, 3)))
    for v in range(AMBIENT):
        x, y = POS[v]
        if v in tags:
            ax.add_patch(Circle((x, y), NODE_R + 0.15, facecolor=COLOR_FOCUS, alpha=0.65,
                                edgecolor="none", zorder=3.5))
        if v not in G.V:
            if ghosts:
                ax.add_patch(Circle((x, y), NODE_R, fill=False, edgecolor=COLOR_GHOST,
                                    linestyle=(0, (2, 2)), linewidth=1.2, zorder=4))
                ax.text(x, y, str(v), ha="center", va="center", fontsize=fontsize * 0.8,
                        color=COLOR_GHOST, zorder=5)
            continue
        cols = [c for P, c in parts if v in P.V] or [COLOR_VERTEX]
        if len(cols) == 1:
            ax.add_patch(Circle((x, y), NODE_R, facecolor=cols[0], edgecolor="#333333",
                                linewidth=1.2, zorder=4))
        else:  # a vertex of both graphs: one vertex of the union
            ax.add_patch(Wedge((x, y), NODE_R, 90, 270, facecolor=cols[0], zorder=4))
            ax.add_patch(Wedge((x, y), NODE_R, 270, 90, facecolor=cols[1], zorder=4))
            ax.add_patch(Circle((x, y), NODE_R, fill=False, edgecolor="#333333",
                                linewidth=1.2, zorder=4.1))
        ax.text(x, y, str(v), ha="center", va="center", fontsize=fontsize, fontweight="bold",
                color="white", zorder=5)
    for v, label in tags.items():
        x, y = POS[v]
        tx = x + (0.62 if x < 0 else -0.62)  # inside, towards the middle
        ax.text(tx, y + (0.38 if y > 0 else -0.38), label, ha="center", va="center",
                fontsize=fontsize * 0.68, fontweight="bold", color="#5A4500", zorder=6,
                bbox=dict(boxstyle="round,pad=0.15", fc="#FFF4C2", ec=COLOR_FOCUS))


def frame(ax) -> None:
    ax.set_xlim(*XLIM)
    ax.set_ylim(*YLIM)
    ax.set_aspect("equal")
    ax.set_xticks([])
    ax.set_yticks([])


def style_box(ax, gold: bool) -> None:
    """Gold background and border for a panel the current step is about."""
    for sp in ax.spines.values():
        sp.set_visible(True)
        sp.set_edgecolor(COLOR_FOCUS if gold else "#D0D0D0")
        sp.set_linewidth(2.6 if gold else 1.0)
    ax.set_facecolor("#FFF9E3" if gold else "white")


def arrow_rad(v: int) -> float:
    """Curvature of a map arrow starting at label v (top arrows bow up, bottom ones down)."""
    return -0.07 if POS[v][1] > 0 else 0.07


def map_arrows(fig, axA, axB, f: dict, color: str = "#8A6A00",
               linestyle=(0, (4, 2)), bend: float = 1.0) -> list:
    """Dashed arrows v ↦ f(v) from a picture axA to a picture axB."""
    out = []
    for v, w in sorted(f.items()):
        rad = bend * arrow_rad(v)
        c = ConnectionPatch(xyA=POS[v], coordsA=axA.transData, xyB=POS[w],
                            coordsB=axB.transData, arrowstyle="-|>", mutation_scale=14,
                            color=color, linewidth=1.6, linestyle=linestyle,
                            shrinkA=13, shrinkB=13, connectionstyle=f"arc3,rad={rad}",
                            zorder=10, alpha=0.9)
        fig.add_artist(c)
        out.append(c)
    return out


def arrow_points(fig, axA, axB, v: int, w: int, n: int = 40,
                 bend: float = 1.0) -> list[tuple[float, float]]:
    """Points (figure fraction) along the arrow v ↦ w drawn by `map_arrows` (arc3 curve)."""
    for ax in (axA, axB):
        ax.apply_aspect()
    (x1, y1) = axA.transData.transform(POS[v])
    (x2, y2) = axB.transData.transform(POS[w])
    rad = bend * arrow_rad(v)
    cx, cy = (x1 + x2) / 2 + rad * (y2 - y1), (y1 + y2) / 2 - rad * (x2 - x1)
    inv = fig.transFigure.inverted()
    pts = []
    for i in range(n + 1):
        t = i / n
        pts.append(((1 - t) ** 2 * x1 + 2 * (1 - t) * t * cx + t ** 2 * x2,
                    (1 - t) ** 2 * y1 + 2 * (1 - t) * t * cy + t ** 2 * y2))
    return [tuple(q) for q in inv.transform(pts)]


def draw_map(ax, G: SG, H: SG, f: dict, fs: float = 9.5, title: str | None = None) -> dict:
    """The bipartite picture of a map f : G.V → H.V with its verdict. Returns the verdict."""
    ax.clear()
    ax.set_xlim(0, 1)
    ax.set_ylim(0, 1)
    ax.axis("off")
    dom, cod = sorted(G.V), sorted(H.V)
    k = max(len(dom), len(cod))
    gap = 0.5 / max(k - 1, 1)
    ys = [0.74 - i * gap for i in range(k)]
    # centre the shorter column
    off_d = (k - len(dom)) / 2 * gap
    off_c = (k - len(cod)) / 2 * gap
    pd = {v: (0.07, ys[i] - off_d) for i, v in enumerate(dom)}
    pc = {w: (0.33, ys[i] - off_c) for i, w in enumerate(cod)}
    vd = map_verdict(G, H, f)
    hits, inj, onto, edges, iso = vd["hits"], vd["inj"], vd["onto"], vd["edges"], vd["iso"]
    if title:
        ax.text(0.0, 0.98, title, fontsize=fs + 0.5, fontweight="bold", va="top")
    ax.text(0.07, 0.86, "V(G₁∪G₂)", ha="center", fontsize=fs - 1, color="#555555")
    ax.text(0.33, 0.86, "V(H₁∪H₂)", ha="center", fontsize=fs - 1, color="#555555")
    for v in dom:
        w = f[v]
        bad = len(hits[w]) > 1
        ax.annotate("", xy=pc[w], xytext=pd[v],
                    arrowprops=dict(arrowstyle="-|>", color=COLOR_WARN if bad else "#8A6A00",
                                    lw=2, shrinkA=10, shrinkB=10, mutation_scale=14))
    msize = fs * 2.1  # round markers (the axes are not square)
    for v, (x, y) in pd.items():
        ax.plot([x], [y], marker="o", markersize=msize, color=COLOR_VERTEX, zorder=4)
        ax.text(x, y, str(v), ha="center", va="center", color="white", fontsize=fs,
                fontweight="bold", zorder=5)
    for w, (x, y) in pc.items():
        missed = not hits[w]
        ax.plot([x], [y], marker="o", markersize=msize, color=COLOR_VERTEX, zorder=4,
                markeredgecolor=COLOR_WARN if missed else COLOR_VERTEX,
                markeredgewidth=2.5 if missed else 1)
        ax.text(x, y, str(w), ha="center", va="center", color="white", fontsize=fs,
                fontweight="bold", zorder=5)
        if missed:
            ax.text(x + 0.05, y, "not hit", va="center", fontsize=fs - 1.5, color=COLOR_WARN)
    missed = [w for w in cod if not hits[w]]
    shared = [w for w in cod if len(hits[w]) > 1]
    lines = [
        (f"f: {fmt_map(f)}", COLOR_TEXT, "bold"),
        (f"one-to-one? {'yes' if inj else 'no: ' + ', '.join(map(str, shared)) + ' hit twice'}",
         COLOR_OK if inj else COLOR_WARN, "normal"),
        (f"onto? {'yes' if onto else 'no: ' + ', '.join(map(str, missed)) + ' not hit'}",
         COLOR_OK if onto else COLOR_WARN, "normal"),
        (f"edge condition? {'yes' if edges else 'no'}", COLOR_OK if edges else COLOR_WARN,
         "normal"),
        ("isomorphism ✓" if iso else "NOT an isomorphism ✗", COLOR_OK if iso else COLOR_WARN,
         "bold"),
    ]
    c = map_counts(G, H)
    for i, (t, col, fw) in enumerate(lines):
        ax.text(0.5, 0.84 - i * 0.1, t, fontsize=fs, color=col, fontweight=fw, va="center")
    ax.text(0.5, 0.36, textwrap.fill(MAP_WORDS, int(50 * 9.5 / fs)), fontsize=fs - 1.5,
            color="#555555", va="top", linespacing=1.3)
    summary = (f"All {c['total']} maps: {c['inj']} one-to-one, {c['onto']} onto, "
               f"{c['iso']} isomorphisms.")
    if len(dom) < len(cod):
        summary += (f" Pigeonhole: {len(dom)} arrows cannot reach {len(cod)} different dots, "
                    "so no map is onto.")
    ax.text(0.0, 0.05, textwrap.fill(summary, int(70 * 9.5 / fs)), fontsize=fs - 0.5,
            color=COLOR_TEXT, va="center", style="italic")
    return dict(vd, missed=missed)


MAP_WORDS = ("one-to-one = no two arrows hit the same target;  onto = every target is hit;  "
             "bijection = both (a perfect pairing)")


def map_verdict(G: SG, H: SG, f: dict) -> dict:
    """Is f : G.V → H.V one-to-one, onto, edge-preserving, an isomorphism?"""
    cod = sorted(H.V)
    hits = {w: [v for v in sorted(G.V) if f.get(v) == w] for w in cod}
    inj = len(set(f.values())) == len(f)
    onto = all(hits[w] for w in cod)
    edges = edge_condition(G, H, f)
    return dict(hits=hits, inj=inj, onto=onto, edges=edges, iso=inj and onto and edges,
                missed=[w for w in cod if not hits[w]])


def legend_entries(gold: bool = True) -> tuple[list, list]:
    """(handles, labels). The 'edge in both' swatch is orange with purple dashes on top,
    exactly as such an edge is drawn. The gold item only makes sense in the explorer."""
    both = (Line2D([], [], color=COLOR_ONE, linewidth=4),
            Line2D([], [], color=COLOR_TWO, linewidth=4, linestyle=(0, (3, 3))))
    out = [
        (Patch(facecolor=COLOR_ONE, edgecolor="#333333"), "from G₁ / H₁"),
        (Patch(facecolor=COLOR_TWO, edgecolor="#333333"), "from G₂ / H₂"),
        (both, "edge in both (one edge)"),
        (Line2D([], [], marker="o", markersize=11, markerfacecolor="white", linestyle="none",
                markeredgecolor=COLOR_GHOST), "label of Fin 4, not a vertex"),
        (Line2D([], [], color="#8A6A00", linewidth=1.6, linestyle=(0, (4, 2))),
         "vertex map f"),
    ]
    if gold:
        out.append((Patch(facecolor="#FFF9E3", edgecolor=COLOR_FOCUS, linewidth=2),
                    "gold: this step"))
    return [h for h, _ in out], [lab for _, lab in out]


# ---------------------------------------------------------------------------
# 5. Static summary figure (visualizations/supp28.png)
# ---------------------------------------------------------------------------

def build_figure(stats: dict) -> plt.Figure:
    G1, G2, H1, H2 = (LEAN_GRAPHS[r] for r in ROLES)
    UG, UH = union(G1, G2), union(H1, H2)
    fig = plt.figure(figsize=(19, 11.5), facecolor="white")
    gs = GridSpec(3, 1, figure=fig, height_ratios=[0.75, 0.95, 0.62], hspace=0.3,
                  left=0.03, right=0.97, top=0.815, bottom=0.025)
    fig.suptitle("Supplementary Exercise 28:  G₁ ≅ H₁ and G₂ ≅ H₂ do NOT imply "
                 "G₁ ∪ G₂ ≅ H₁ ∪ H₂", fontsize=19, fontweight="bold", color=COLOR_TEXT,
                 y=0.985)
    fig.text(0.5, 0.955, "\"Suppose that G₁ and H₁ are isomorphic and that G₂ and H₂ are "
             "isomorphic. Prove or disprove that G₁ ∪ G₂ and H₁ ∪ H₂ are isomorphic.\"   "
             "Answer: disproved, in Lean as GraphCh10.supp28 (a statement ¬ ∀ …).",
             ha="center", fontsize=10.5, color="#444444")
    fig.text(0.5, 0.936, "One counterexample is enough to disprove a 'for all' claim. The "
             "pictures show it; the Lean proof checks it.  Run  python visualizations/"
             "supp28.py  for the interactive walkthrough.", ha="center", fontsize=10.5,
             color=COLOR_WARN, style="italic")
    handles, labels = legend_entries(gold=False)
    fig.legend(handles, labels, loc="upper center", ncol=5, frameon=False,
               fontsize=10, bbox_to_anchor=(0.5, 0.925), handlelength=2.6)

    # Row 0: the two hypotheses, then the two unions.
    row0 = GridSpecFromSubplotSpec(1, 8, subplot_spec=gs[0], wspace=0.25,
                                   width_ratios=[1, 0.35, 1, 0.25, 1, 0.35, 1, 0.0001])
    specs = [(0, "G₁", G1, None), (2, "H₁", H1, None), (4, "G₂", G2, None),
             (6, "H₂", H2, None)]
    axes = {}
    for col, name, G, _ in specs:
        ax = fig.add_subplot(row0[0, col])
        color = COLOR_ONE if name.endswith("₁") else COLOR_TWO
        draw_sg(ax, G, color)
        frame(ax)
        style_box(ax, False)
        ax.set_title(f"{name} = {LEAN_NAMES[name]}\n{fmt_graph(G)}", fontsize=10.5)
        ax.apply_aspect()  # so get_position() is the drawn box, not the grid cell
        axes[name] = ax
    map_arrows(fig, axes["G₁"], axes["H₁"], {v: v for v in G1.V})
    map_arrows(fig, axes["G₂"], axes["H₂"], shift_map(G2))
    for (a, b, label) in (("G₁", "H₁", "≅ by the identity\n0↦0, 1↦1"),
                          ("G₂", "H₂", f"≅ by v ↦ v + {SHIFT_K}\n{fmt_map(shift_map(G2))}")):
        pa, pb = axes[a].get_position(), axes[b].get_position()
        fig.text((pa.x1 + pb.x0) / 2, (pa.y0 + pa.y1) / 2, label, ha="center", va="center",
                 fontsize=10.5, fontweight="bold", color="#8A6A00")  # between the two arrows
    fig.text(0.5, 0.862, "Hypotheses: both hold (computed and proved in Lean)", ha="center",
             fontsize=13, fontweight="bold")

    # Row 1: the unions, the map picture, and the relabelling table.
    row1 = GridSpecFromSubplotSpec(1, 4, subplot_spec=gs[1], wspace=0.18,
                                   width_ratios=[1, 1, 1.35, 1.5])
    for col, name, (A, B), U in ((0, "G₁ ∪ G₂", (G1, G2), UG), (1, "H₁ ∪ H₂", (H1, H2), UH)):
        ax = fig.add_subplot(row1[0, col])
        draw_sg(ax, U, parts=[(A, COLOR_ONE), (B, COLOR_TWO)])
        frame(ax)
        style_box(ax, False)
        ax.set_title(f"{name}:  {len(U.V)} vertices, {len(U.E)} edge{'s' * (len(U.E) != 1)}"
                     f"\n{fmt_graph(U)}", fontsize=10.5)
        ax.apply_aspect()
        axes[name] = ax
    ax = fig.add_subplot(row1[0, 2])
    draw_map(ax, UG, UH, {0: 0, 1: 1}, fs=10)
    ax.set_title("No bijection V(G₁∪G₂) → V(H₁∪H₂), so not isomorphic", fontsize=11,
                 fontweight="bold")
    sub = GridSpecFromSubplotSpec(2, 3, subplot_spec=row1[0, 3], wspace=0.1, hspace=0.45)
    for i, (pair, (nv, iso)) in enumerate(sorted(stats["relabel"].items())):
        a = fig.add_subplot(sub[i // 3, i % 3])
        h2 = k2(*pair)
        draw_sg(a, union(H1, h2), parts=[(H1, COLOR_ONE), (h2, COLOR_TWO)], fontsize=9)
        frame(a)
        style_box(a, pair == LEAN_H2_PAIR)
        a.set_title(f"H₂ on {fmt_set(pair)}: {nv} vertices\n"
                    f"{'≅ G₁ ∪ G₂ ✓' if iso else '≇ G₁ ∪ G₂'}", fontsize=9.5,
                    color=COLOR_OK if iso else COLOR_WARN)
    pos = row1[0, 3].get_position(fig)
    minis = fig.axes[-6:]  # the six relabelling pictures just drawn
    for m in minis:
        m.apply_aspect()
    top = max(m.get_position().y1 for m in minis)
    fig.text((pos.x0 + pos.x1) / 2, top + 0.042, "Relabel H₂: G₂ ≅ H₂ always, but the "
             "union depends on the overlap", ha="center", fontsize=11, fontweight="bold")
    p0, p1 = axes["G₁ ∪ G₂"].get_position(), axes["H₁ ∪ H₂"].get_position()
    fig.text((p0.x0 + p1.x1) / 2, p0.y1 + 0.06, "Conclusion fails: the unions have "
             "different numbers of vertices", ha="center", fontsize=13, fontweight="bold")

    # Row 2: proof correspondence.
    ax = fig.add_subplot(gs[2])
    ax.axis("off")
    ax.add_patch(plt.Rectangle((0, 0), 1, 1, transform=ax.transAxes, facecolor=COLOR_PANEL,
                               edgecolor="#D0D0D0", linewidth=1))
    left = ["The Lean proof, step by step  (GraphCh10/Exercises/Supp28.lean)",
            "def k2Low / k2High                K₂ on {0, 1} and K₂ on {2, 3}, inside Fin 4",
            "theorem isomorphic_refl           every graph ≅ itself (identity map)",
            "theorem k2Low_isomorphic_k2High   K₂ on {0, 1} ≅ K₂ on {2, 3} via v ↦ v + 2",
            "theorem union_low_low_V, …high_V  V(G₁∪G₂) = {0, 1},  V(H₁∪H₂) = {0, 1, 2, 3}",
            "theorem card_eq_of_isomorphic     isomorphic ⇒ equally many vertices",
            "intro hall; have h₁ h₂ hunion     assume the claim; apply it to the counterexample",
            "have hcard; rw; absurd            so #{0, 1} = #{0, 1, 2, 3}, i.e. 2 = 4: False  ∎"]
    c = stats["counts"]
    right = ["Checked by assertions in this script",
             "• the statement in Supp28.lean is the approved one; graphs parsed from the file",
             "• identity and v ↦ v + 2 are isomorphisms; union vertex sets match the lemmas",
             f"• all {c['total']} maps {{0,1}} → {{0,1,2,3}}: {c['inj']} one-to-one, "
             f"{c['onto']} onto, {c['iso']} isomorphisms (NetworkX agrees: not isomorphic)",
             "• relabelling H₂: the unions are isomorphic only when H₂ sits on {0, 1}",
             f"• all {stats['n_graphs3']}⁴ quadruples of simple graphs inside {{0, 1, 2}}: "
             f"{stats['n_hyp']:,} satisfy",
             f"  the hypotheses, {stats['n_fail']:,} of them break the conclusion "
             "(illustration only)"]
    for x, lines in ((0.015, left), (0.55, right)):
        ax.text(x, 0.92, lines[0], transform=ax.transAxes, fontsize=11.5, fontweight="bold",
                va="top", color=COLOR_TEXT)
        ax.text(x, 0.76, "\n".join(lines[1:]), transform=ax.transAxes, fontsize=9.8,
                va="top", color=COLOR_TEXT, family="DejaVu Sans Mono" if x < 0.5 else None,
                linespacing=1.55)
    return fig


# ---------------------------------------------------------------------------
# 6. Lean source, read from the project (the source of truth)
# ---------------------------------------------------------------------------

def _block(lines: list[str], start: str, end: str, extra: int = 0) -> list[str]:
    """The lines from the unique line starting with `start` to the first later line
    containing `end` (inclusive), plus `extra` more lines."""
    hits = [i for i, ln in enumerate(lines) if ln.strip().startswith(start)]
    assert len(hits) == 1, f"expected exactly one line starting with {start!r}"
    j = next(j for j in range(hits[0], len(lines)) if end in lines[j])
    return [ln.rstrip() for ln in lines[hits[0]:j + 1 + extra]]


def read_lean_sources() -> dict[str, list[str]]:
    """The proof of `supp28`, its helpers and the definitions, read verbatim."""
    proof = _require(PROOF_FILE)
    d = _require(DEFS_FILE)
    defs = [
        "-- GraphCh10/Definitions.lean (excerpt; docstrings omitted)",
        *_block(d, "structure SetSimpleGraph", "loopless : ∀ p ∈ E, ¬ p.IsDiag"),
        "",
        "namespace SetSimpleGraph",
        "",
        *_block(d, "protected def union (G₁ G₂ : SetSimpleGraph α)", "E := G₁.E ∪ G₂.E"),
        "  ...  -- (proofs that the union is again simple)",
        "",
        *_block(d, "instance : Union (SetSimpleGraph α)", "SetSimpleGraph.union"),
        "",
        *_block(d, "def Isomorphic (G₁ : SetSimpleGraph α)",
                "s((f v₁ : β), (f v₂ : β)) ∈ G₂.E ↔"),
    ]
    return {
        "defs": defs,
        "header": _block(proof, "**Answer: the assertion is false.**",
                         "isomorphic, and the assertion fails"),
        "k2": _block(proof, "def k2Low", "-- {2, 3} is not a loop because 2 ≠ 3", extra=1),
        "refl": _block(proof, "theorem isomorphic_refl", "exact Iff.rfl"),
        "iso": _block(proof, "theorem k2Low_isomorphic_k2High",
                      "rcases hx with rfl | rfl <;> rcases hy"),
        "unionV": _block(proof, "theorem union_low_low_V", "tauto"),
        "card": _block(proof, "theorem card_eq_of_isomorphic", "_ = t.card := Fintype.card_coe t"),
        "main": _block(proof, "theorem supp28", "exact absurd hcard (by decide)"),
    }


SOURCE_NAMES = {
    "defs": "GraphCh10/Definitions.lean",
    "header": "Supp28.lean  ·  file comment",
    "k2": "Supp28.lean  ·  the two copies of K₂",
    "refl": "Supp28.lean  ·  helper isomorphic_refl",
    "iso": "Supp28.lean  ·  helper k2Low_isomorphic_k2High",
    "unionV": "Supp28.lean  ·  helpers union_low_low_V, union_low_high_V",
    "card": "Supp28.lean  ·  helper card_eq_of_isomorphic",
    "main": "Supp28.lean  ·  the main theorem",
}


# ---------------------------------------------------------------------------
# 7. The walkthrough
# ---------------------------------------------------------------------------
# Each step: part, title, which code to show, `anchors` (substrings that must each match
# exactly one line) and `ranges` ((first, last) substrings: every line in between is
# highlighted), a focus kind (what to highlight in the picture), and two explanations.
# `math` may be a function of (explorer, focus).

P1, P2, P3, P4, P5 = ("Part 1 · What the exercise says", "Part 2 · The counterexample",
                      "Part 3 · Lean: the building blocks", "Part 4 · Lean: the main proof",
                      "Part 5 · Picture vs. proof")

RELABELLED = ("⚠ H₂ is relabelled to K₂ on {}: the picture no longer shows the Lean "
              "counterexample (H₂ = K₂ on {}). Press 'Reset' to go back. ")


def _union_sentence(ex) -> str:
    UG, UH = ex.unions
    iso = isomorphic(UG, UH)
    return (f"G₁ ∪ G₂ has V = {fmt_set(UG.V)} ({len(UG.V)} vertices) and H₁ ∪ H₂ has "
            f"V = {fmt_set(UH.V)} ({len(UH.V)} vertices), so they are "
            f"{'isomorphic' if iso else 'NOT isomorphic'}")


def _sizes_sentence(ex) -> str:
    """Vertex counts of the two unions (no verdict: used before isomorphism is taught)."""
    UG, UH = ex.unions
    return (f"G₁ ∪ G₂ has V = {fmt_set(UG.V)} ({len(UG.V)} vertices) and H₁ ∪ H₂ has "
            f"V = {fmt_set(UH.V)} ({len(UH.V)} vertices)")


def _pigeon_sentence(ex) -> str:
    """What the map panel shows for the CURRENT unions."""
    UG, UH = ex.unions
    m, n = len(UG.V), len(UH.V)
    c = map_counts(UG, UH)
    if m < n:
        return (f"Here f has {m} arrows and V(H₁ ∪ H₂) has {n} dots. Pigeonhole: {m} arrows "
                f"cannot reach {n} different dots, so at most {m} of the {n} targets are "
                f"hit and no map is onto. Of all {c['total']} maps, {c['onto']} are onto.")
    return (f"Right now both unions have {m} vertices, so maps CAN be onto: of all "
            f"{c['total']} maps, {c['bij']} are bijections and {c['iso']} are isomorphisms. "
            f"(In the Lean example the unions have 2 and 4 vertices, and none is onto.)")


STEPS: list[dict] = [
    dict(
        part=P1, title="Simple graphs as pairs (V, E)", code="defs",
        ranges=[("structure SetSimpleGraph", "loopless : ∀ p ∈ E, ¬ p.IsDiag")],
        focus="simple",
        math=lambda ex, f: (
            "A simple graph G = (V, E) is a set V of vertices (the dots) and a set E of "
            "edges. Each edge joins two DIFFERENT vertices (no loops), and two vertices are "
            "joined at most once (no multiple edges). In this exercise every vertex is one "
            "of the four labels 0, 1, 2, 3. Gold: G₁ has V = {0, 1} and one edge, "
            "E = {{0, 1}}. The faint dashed circles are labels that are NOT vertices of "
            "this graph. Labels matter later: a union is formed label by label."),
        lean=("`structure SetSimpleGraph (α : Type u)` bundles four fields (`Type u` just "
              "means 'any type'; u is a technical size label). `V : Set α` is "
              "the vertex set, a set of elements of the 'ambient' type α (here α = Fin 4, "
              "the numbers {0, 1, 2, 3}). `E : Set (Sym2 α)` is the edge set. `Sym2 α` is "
              "the type of unordered pairs, written s(u, w), so s(0, 1) = s(1, 0). "
              "`edge_sub` says both ends of every edge are in V, and `loopless` says no "
              "edge is a loop s(v, v) (`IsDiag`). Because E is a set, the same edge cannot "
              "appear twice."),
    ),
    dict(
        part=P1, title="Union: put two graphs on top of each other", code="defs",
        ranges=[("protected def union", "E := G₁.E ∪ G₂.E")],
        anchors=["instance : Union (SetSimpleGraph α)"], focus="unions",
        math=lambda ex, f: (
            "The union G₁ ∪ G₂ is the graph (V₁ ∪ V₂, E₁ ∪ E₂): every vertex and every "
            "edge that appears in at least one of the two graphs. A label used by both "
            "graphs gives ONE vertex of the union (half orange, half purple), and an edge in "
            "both graphs gives ONE edge (dashed two-colour line). Gold: the two unions of "
            f"this exercise. {_sizes_sentence(ex)}."),
        lean=("`protected def union (G₁ G₂ : SetSimpleGraph α)` builds a new graph with "
              "`V := G₁.V ∪ G₂.V` and `E := G₁.E ∪ G₂.E`. It also needs proofs that the "
              "result is again simple; they are left out of this panel. The `instance : "
              "Union …` line lets us write `G₁ ∪ G₂`. Both graphs must live in the SAME "
              "ambient type α, otherwise V₁ ∪ V₂ would not make sense."),
    ),
    dict(
        part=P1, title="Isomorphism: rename the vertices, keep the edges", code="defs",
        ranges=[("def Isomorphic", "s((f v₁ : β), (f v₂ : β)) ∈ G₂.E ↔")], focus="iso2",
        math=lambda ex, f: (
            "G and H are isomorphic (G ≅ H) if there is a one-to-one correspondence f from "
            "the vertices of G to the vertices of H, also called a bijection: no two "
            "vertices of G go to the same vertex of H, and every vertex of H is hit, "
            "such that {f(v₁), f(v₂)} is an edge of H exactly when {v₁, v₂} is an edge of "
            "G. So isomorphic graphs have the same shape and differ only in the names of "
            f"their vertices. Gold: G₂ ≅ H₂ by f: {fmt_map(f['f'])} (dashed arrows). "
            f"The definition checks every pair v₁, v₂. {f['pair_text']} "
            "('Next example' shows the next pair.)"),
        lean=("`def Isomorphic G₁ G₂ : Prop := ∃ f : G₁.V ≃ G₂.V, ∀ v₁ v₂ : G₁.V, "
              "s((f v₁ : β), (f v₂ : β)) ∈ G₂.E ↔ s((v₁ : α), (v₂ : α)) ∈ G₁.E`. `A ≃ B` "
              "(an `Equiv`) is a bijection: a map together with its inverse. `G₁.V ≃ G₂.V` "
              "uses the vertex SETS as types: an element of `G₁.V` is a label together with "
              "a proof that it lies in V, and `(v₁ : α)` keeps just the label. `↔` is 'if "
              "and only if'. The two graphs may live in different ambient types α and β."),
    ),
    dict(
        part=P1, title="How to read the Lean statement", code="main",
        ranges=[("theorem supp28", "(G₁ ∪ G₂).Isomorphic (H₁ ∪ H₂) := by")],
        focus="statement",
        math=lambda ex, f: (
            "Lean is a program that checks proofs step by step. A theorem has a name "
            "(supp28), a statement after the colon, and after `:= by` a proof made of "
            "commands called tactics. Here the statement reads: 'it is NOT true that for all "
            "types α, β, all graphs G₁, G₂ in α and H₁, H₂ in β, if G₁ ≅ H₁ and G₂ ≅ H₂ "
            "then G₁ ∪ G₂ ≅ H₁ ∪ H₂'. The part after ¬ is exactly the exercise's claim, "
            "with every hypothesis kept. So supp28 says: the claim is false."),
        lean=("Symbols: `¬` not, `∀` for all, `→` implies (read `A → B → C` as 'if A and B "
              "then C'), `∪` union. `(α β : Type)` means α and β are any types, i.e. any "
              "collections of labels. `G₁.Isomorphic H₁` is `Isomorphic` applied to G₁ and "
              "H₁. G₁, G₂ share the type α so that G₁ ∪ G₂ makes sense, and likewise H₁, H₂ "
              "share β."),
    ),
    dict(
        part=P1, title="Prove or disprove: one counterexample is enough", code="main",
        anchors=["¬ ∀ (α β : Type)"], focus="four",
        math=lambda ex, f: (
            "The claim talks about EVERY choice of four graphs. To show it is false it is "
            "enough to find ONE choice where both hypotheses hold (G₁ ≅ H₁, G₂ ≅ H₂) but the "
            "conclusion fails (G₁ ∪ G₂ is not ≅ H₁ ∪ H₂). Such a choice is a "
            "counterexample. So the answer to 'prove or disprove' is: disproved. (Proving "
            "a 'for all' claim would need an argument covering every case; here one well "
            "chosen case does the job.)"),
        lean=("In Lean, `¬ P` is defined as `P → False`: 'if P then something impossible'. "
              "So to prove `¬ (∀ …)`, the proof assumes the ∀-statement (tactic "
              "`intro hall`) and must reach `False`, a contradiction. It does so by applying "
              "`hall` to the counterexample of Part 2 and deriving 2 = 4 (Part 4)."),
    ),
    dict(
        part=P2, title="The four graphs", code="header",
        anchors=["G₁ = G₂ = H₁ = K₂ on {0, 1}", "H₂ = K₂ on {2, 3}"], focus="four",
        math=lambda ex, f: (
            "K₂ is the graph with two vertices and one edge between them. Take G₁ = G₂ = "
            f"H₁ = K₂ on the labels {{0, 1}} and H₂ = K₂ on {fmt_set(ex.h2_pair)}. "
            "Hypothesis 1: G₁ ≅ H₁, since they are the same graph (rename nothing: "
            f"0↦0, 1↦1). Hypothesis 2: G₂ ≅ H₂ by {fmt_map(ex.f2)}, which sends the edge "
            f"{{0, 1}} to the edge {fmt_set(ex.h2_pair)}. Both hold: "
            f"{'✓' if isomorphic(ex.G['G₁'], ex.G['H₁']) and isomorphic(ex.G['G₂'], ex.G['H₂']) else '✗'} "
            "(computed by the script from the definition)."),
        lean=("In the Lean file these graphs are `k2Low` (K₂ on {0, 1}) and `k2High` (K₂ on "
              "{2, 3}), both inside the ambient type `Fin 4` = {0, 1, 2, 3}. So α = β = "
              "Fin 4, G₁ = G₂ = H₁ = `k2Low` and H₂ = `k2High`. The file comment above, which "
              "the Lean proof follows, gives the paper version."),
    ),
    dict(
        part=P2, title="The unions have different sizes", code="header",
        ranges=[("3. G₁ ∪ G₂ = ({0, 1}, {{0, 1}}) has 2 vertices", "isomorphic, and the assertion")],
        focus="unions",
        math=lambda ex, f: (
            "In the Lean example, G₁ and G₂ sit on the SAME labels {0, 1}, so G₁ ∪ G₂ stacks "
            "them: it is K₂ again, 2 vertices and 1 edge. H₁ (on {0, 1}) and H₂ (on {2, 3}) "
            "sit on DIFFERENT labels, so H₁ ∪ H₂ is two separate copies of K₂: 4 vertices "
            "and 2 edges. An isomorphism matches "
            "vertices one-to-one, so isomorphic graphs have equally many vertices. "
            f"In the picture now: {_union_sentence(ex)}. Key idea: a union depends on how "
            "the graphs OVERLAP "
            "(which labels they share); an isomorphism forgets the labels, so it cannot "
            "control the overlap."),
        lean=("Items 3 and 4 of the file comment. In Lean, item 3 is the pair of helpers "
              "`union_low_low_V` and `union_low_high_V`, and item 4 is the helper "
              "`card_eq_of_isomorphic` (Part 3)."),
    ),
    dict(
        part=P2, title="Try it: relabel H₂, try maps", code="header",
        anchors=["4. An isomorphism is in particular"], focus="relabel",
        math=lambda ex, f: (
            "Use the 'Relabel H₂' buttons. Every choice is a copy of K₂, so G₂ ≅ H₂ "
            "always holds. But H₁ ∪ H₂ changes: sharing both labels {0, 1} with H₁ gives 2 "
            "vertices, sharing one label gives 3 vertices (a path), sharing none gives 4. "
            f"Right now: {_union_sentence(ex)}. Only H₂ on {{0, 1}} makes the unions "
            "isomorphic. In the map panel, press f(0) ▸, f(1) ▸ or 'Next map ▸'. "
            f"{_pigeon_sentence(ex)}"),
        lean=("Nothing in this step is Lean. The script recomputes the unions and checks "
              "every map by brute force, straight from the definitions of union and "
              "isomorphism. The Lean proof only needs the single choice H₂ = K₂ on {2, 3}."),
    ),
    dict(
        part=P3, title="Tactic cheat sheet (come back to it)", code="main",
        anchors=["intro hall"], focus="four",
        math=lambda ex, f: (
            "You do not need to memorise tactics: 'What it means' always gives the idea, and "
            "'In Lean' shows how each line carries it out. Press ◀ Previous to come back here "
            "whenever a tactic name is unfamiliar."),
        lean=("• `⟨a, b⟩` (angle brackets) builds a pair, or unpacks one after rintro / "
              "obtain\n"
              "• `intro h` / `rintro ⟨a, b⟩`: assume the 'if' part and call it h (rintro "
              "also unpacks it)\n"
              "• `exact t`: t proves the goal, done     • `have h : P := t`: prove P, name it h\n"
              "• `refine ⟨w, ?_⟩`: give the witness w now, prove the rest ?_ later\n"
              "• `obtain ⟨f, -⟩ := h`: unpack h, keep f, throw away the second part (-)\n"
              "• `rcases h with rfl | rfl`: one case for each side of an 'or'\n"
              "• `change P`: restate the goal in an equivalent, unfolded form\n"
              "• `rw [h]`: replace the left side of h by its right side (`at hc`: inside hc)\n"
              "• `simp only [rules]`: simplify using exactly these rules   • `ext x`: sets are "
              "equal if they have the same members\n"
              "• `tauto`: finish by pure logic   • `decide`: let Lean compute a yes/no fact\n"
              "• `calc a = b := … _ = c := …`: a chain a = b = c   • `absurd h hn`: h and "
              "not-h give anything"),
    ),
    dict(
        part=P3, title="k2Low and k2High: two copies of K₂", code="k2",
        ranges=[("def k2Low", "E := {s(0, 1)}"), ("def k2High", "E := {s(2, 3)}")],
        anchors=["-- the endpoints of {0, 1} are 0 and 1", "-- {0, 1} is not a loop because 0 ≠ 1"],
        focus="four",
        math=lambda ex, f: (
            "These are the graphs of the counterexample: K₂ on {0, 1} (G₁, G₂ and H₁) and K₂ "
            "on {2, 3} (H₂). To count as simple graphs, each must pass two checks: both "
            "ends of its edge are vertices, and its edge is not a loop. For K₂ on {0, 1}: "
            "the ends 0 and 1 are in V = {0, 1}, and 0 ≠ 1."),
        lean=("`def k2Low : SetSimpleGraph (Fin 4) where` fills in the four fields. "
              "`V := {0, 1}`, `E := {s(0, 1)}`. For `edge_sub`, `rintro p rfl x hx` takes the "
              "edge p (and `rfl` replaces it by s(0, 1)) and an end x; `Sym2.mem_iff` turns "
              "'x is an end of s(0, 1)' into 'x = 0 or x = 1', and `Or.inl rfl` / `Or.inr rfl` "
              "show 0 and 1 are in {0, 1}. For `loopless`, `decide` lets Lean compute that "
              "s(0, 1) is not of the form s(v, v). `k2High` is the same on {2, 3}."),
    ),
    dict(
        part=P3, title="Helper: every graph is isomorphic to itself", code="refl",
        ranges=[("theorem isomorphic_refl", "exact Iff.rfl")], focus="iso1",
        math=lambda ex, f: (
            "This gives hypothesis 1, G₁ ≅ H₁: G₁ and H₁ are the same graph, and the "
            "identity map (every vertex to itself, the dashed arrows) is an isomorphism. "
            "It is a bijection, and it sends each pair {v₁, v₂} to itself, so 'edge in H₁' "
            "and 'edge in G₁' are literally the same statement."),
        lean=("The goal `G.Isomorphic G` is an `∃ f, …`. `refine ⟨Equiv.refl G.V, ?_⟩` "
              "offers the identity bijection `Equiv.refl` as f and leaves the edge "
              "condition `?_`. `intro v₁ v₂` takes two vertices. The goal is now "
              "`s(v₁, v₂) ∈ G.E ↔ s(v₁, v₂) ∈ G.E`, and `Iff.rfl` proves 'P ↔ P'. The lemma "
              "is stated for every graph G, so it can be used with G = `k2Low`."),
    ),
    dict(
        part=P3, title="Helper: K₂ on {0, 1} ≅ K₂ on {2, 3}, the map", code="iso",
        ranges=[("let f : k2Low.V ≃ k2High.V", "rcases hy with rfl | rfl <;> rfl }")],
        focus="bij",
        math=lambda ex, f: (
            "This gives hypothesis 2, G₂ ≅ H₂. The map is v ↦ v + 2: 0 ↦ 2 and 1 ↦ 3 "
            "(gold dashed arrows). Its inverse is w ↦ w − 2: 2 ↦ 0 and 3 ↦ 1 (blue dotted "
            "arrows, going back). A map that has an inverse undoing it is a bijection. This "
            "step only builds the map; the next step checks the edges."),
        lean=("`let f : k2Low.V ≃ k2High.V := { toFun, invFun, left_inv, right_inv }` "
              "builds the bijection from four pieces. An element x of `k2Low.V` is a pair "
              "⟨label, proof⟩ (angle brackets): `x.1` is the label and `x.2` a proof that it "
              "lies in {0, 1}. So `toFun := fun x => ⟨x.1 + 2, …⟩` makes the new pair: label "
              "x.1 + 2 plus a proof that it lies in {2, 3} (`rcases hx with rfl | rfl` tries "
              "x = 0 and x = 1). `invFun` subtracts 2. `left_inv`, `right_inv` prove the two "
              "maps undo each other. `Subtype.ext` says two such pairs are equal when their "
              "labels are equal, and `rfl` checks (0 + 2) − 2 = 0 etc. by computing in Fin 4."),
    ),
    dict(
        part=P3, title="Helper: K₂ on {0, 1} ≅ K₂ on {2, 3}, the edges", code="iso",
        ranges=[("refine ⟨f, ?_⟩", "rcases hx with rfl | rfl <;> rcases hy")], focus="iso2",
        math=lambda ex, f: (
            "Now the edge condition (Lean example, f = v ↦ v + 2): for all v₁, v₂ in "
            "{0, 1}, {f(v₁), f(v₂)} = {2, 3} exactly when {v₁, v₂} = {0, 1}. There are only "
            "four ordered pairs to check. "
            f"{f['pair_text']} ('Next example' shows the next pair.)"),
        lean=("`refine ⟨f, ?_⟩` offers f and leaves the edge condition. `rintro ⟨x, hx⟩ "
              "⟨y, hy⟩` takes v₁ = x, v₂ = y with proofs hx, hy that they are in {0, 1}. "
              "`change` unfolds the goal to `s(x + 2, y + 2) ∈ {s(2, 3)} ↔ s(x, y) ∈ "
              "{s(0, 1)}`, and `simp only [Set.mem_singleton_iff]` turns '∈ {p}' into '= p'. "
              "`rcases … <;> rcases …` makes the four cases (x, y ∈ {0, 1}), and `decide` "
              "checks each one by computation."),
    ),
    dict(
        part=P3, title="Helper: the two vertex sets", code="unionV",
        ranges=[("theorem union_low_low_V", "tauto")], focus="unions",
        math=lambda ex, f: (
            "V(G₁ ∪ G₂) = {0, 1} ∪ {0, 1} = {0, 1}: uniting a set with itself changes "
            "nothing. V(H₁ ∪ H₂) = {0, 1} ∪ {2, 3} = {0, 1, 2, 3}. These are the vertex "
            "sets in the gold pictures."),
        lean=("The sets on the right are written as `Finset`s (finite sets that Lean can "
              "count); `↑` turns a `Finset` into an ordinary set. First lemma: `change` "
              "unfolds `(k2Low ∪ k2Low).V` to `{0, 1} ∪ {0, 1}`; `rw [Set.union_self, …]` "
              "uses A ∪ A = A and rewrites `↑{0, 1}` as `{0, 1}`. Second lemma: `ext x` "
              "says 'compare members'; `simp only […]` turns both sides into 'x = 0 ∨ x = 1 "
              "∨ x = 2 ∨ x = 3' (`∨` is 'or'), and `tauto` finishes by logic."),
    ),
    dict(
        part=P3, title="Helper: isomorphic ⇒ equally many vertices", code="card",
        ranges=[("theorem card_eq_of_isomorphic", "_ = t.card := Fintype.card_coe t")],
        focus="map",
        math=lambda ex, f: (
            "If G ≅ H, then G and H have the same number of vertices: the isomorphism "
            "contains a one-to-one correspondence between the vertex sets, and finite sets "
            "in one-to-one correspondence have equally many elements. Only the bijection "
            "is used, not the edge condition. Turned around: graphs with different numbers "
            f"of vertices cannot be isomorphic. {_pigeon_sentence(ex)}"),
        lean=("Hypotheses: `hG : G.V = ↑s`, `hH : H.V = ↑t` (the vertex sets are the finite "
              "sets s, t) and `hiso`. `obtain ⟨f, -⟩ := hiso` keeps the bijection f and drops "
              "the edge condition. `Equiv.subtypeEquivRight` says: two sets with the same "
              "members are in bijection (each element is matched with itself), so eG : "
              "G.V ≃ ↑s (by `rw [hG]`). `.symm` reverses a bijection and `.trans` does one "
              "bijection, then the other: `eG.symm.trans (f.trans eH)` goes s → G.V → H.V → t, "
              "one bijection e. The `calc` chain: s.card = (size of s) = (size of t) = "
              "t.card, where `Fintype.card_congr e` is 'a bijection preserves size'."),
    ),
    dict(
        part=P4, title="intro hall: assume the claim", code="main",
        anchors=["intro hall"], focus="statement",
        math=lambda ex, f: (
            "The proof is by contradiction. Suppose the claim were true for all graphs. We "
            "will apply it to the counterexample and reach an impossible statement. That "
            "shows the claim cannot be true."),
        lean=("The goal is `¬ ∀ …`, which means `(∀ …) → False`. `intro hall` assumes the "
              "∀-statement, names it `hall`, and leaves the goal `False`. From now on `hall` "
              "is a machine: give it α, β, G₁, G₂, H₁, H₂ and proofs of G₁ ≅ H₁ and G₂ ≅ H₂, "
              "and it returns a proof of G₁ ∪ G₂ ≅ H₁ ∪ H₂."),
    ),
    dict(
        part=P4, title="h₁, h₂: the hypotheses hold", code="main",
        anchors=["have h₁ : k2Low.Isomorphic k2Low", "have h₂ : k2Low.Isomorphic k2High"],
        focus="four",
        math=lambda ex, f: (
            "For our four graphs both hypotheses are true: G₁ ≅ H₁ by the identity and "
            f"G₂ ≅ H₂ by {fmt_map(shift_map(LEAN_GRAPHS['G₂']))} (the dashed arrows)."),
        lean=("`have h₁ : k2Low.Isomorphic k2Low := isomorphic_refl k2Low` uses the general "
              "helper with G = `k2Low`. `have h₂ : k2Low.Isomorphic k2High := "
              "k2Low_isomorphic_k2High` uses the specific helper. Each `have` adds a proven "
              "fact with a name, ready to be passed to `hall`."),
    ),
    dict(
        part=P4, title="hunion: what the claim would give", code="main",
        anchors=["have hunion", "hall (Fin 4) (Fin 4) k2Low k2Low k2Low k2High h₁ h₂"],
        focus="unions",
        math=lambda ex, f: (
            "Feeding our counterexample into the assumed claim, it would follow that "
            "G₁ ∪ G₂ ≅ H₁ ∪ H₂. This is what we now show to be impossible. "
            f"(In fact {_union_sentence(ex)}.)"),
        lean=("`hall (Fin 4) (Fin 4) k2Low k2Low k2Low k2High h₁ h₂` fills in α = Fin 4, "
              "β = Fin 4, G₁ = k2Low, G₂ = k2Low, H₁ = k2Low, H₂ = k2High (in the order of "
              "the statement) and the two hypothesis proofs. The result is "
              "`hunion : (k2Low ∪ k2Low).Isomorphic (k2Low ∪ k2High)`. It holds only under "
              "the assumption `hall`."),
    ),
    dict(
        part=P4, title="hcard: equally many vertices?", code="main",
        anchors=["have hcard", "card_eq_of_isomorphic union_low_low_V union_low_high_V hunion"],
        focus="map",
        math=lambda ex, f: (
            "An isomorphism contains a one-to-one correspondence of the vertices, so "
            "#{0, 1} would equal #{0, 1, 2, 3} (# = 'number of elements'), i.e. 2 = 4. "
            f"The map panel shows the counting: {_pigeon_sentence(ex)}"),
        lean=("`card_eq_of_isomorphic union_low_low_V union_low_high_V hunion` uses the "
              "helper with s = {0, 1}, t = {0, 1, 2, 3}: the two vertex-set lemmas provide "
              "`hG` and `hH`, and `hunion` provides `hiso`. The result is `hcard : "
              "({0, 1} : Finset (Fin 4)).card = ({0, 1, 2, 3} : Finset (Fin 4)).card`."),
    ),
    dict(
        part=P4, title="2 = 4 is false: contradiction  ∎", code="main",
        ranges=[("have h2 : ({0, 1} : Finset (Fin 4)).card = 2", "exact absurd hcard (by decide)")],
        focus="map",
        math=lambda ex, f: (
            "{0, 1} has 2 elements and {0, 1, 2, 3} has 4, so hcard says 2 = 4, which is "
            "false. The assumption 'the claim holds for all graphs' led to a contradiction, "
            "so the claim is false: G₁ ≅ H₁ and G₂ ≅ H₂ do not imply G₁ ∪ G₂ ≅ H₁ ∪ H₂. ∎"),
        lean=("`have h2 : … .card = 2 := by decide` and `h4 : … = 4` let Lean count the "
              "finite sets. `rw [h2, h4] at hcard` rewrites inside `hcard`, which becomes "
              "`hcard : 2 = 4`. `(by decide)` proves `¬ (2 = 4)`, and `absurd hcard (…)` turns "
              "a fact and its negation into anything at all, in particular the goal `False`. "
              "The proof is complete."),
    ),
    dict(
        part=P5, title="The picture illustrates; Lean proves", code="main", anchors=[],
        focus="all",
        math=lambda ex, f: (
            "Here one example really is enough, because the claim was a 'for all' and we "
            "disproved it. Still, the pictures only illustrate: the facts that the "
            "hypotheses hold, that the unions have 2 and 4 vertices and that 2 ≠ 4 are "
            "checked by Lean. For curiosity, the script searched all "
            f"{ex.stats['n_graphs3']}⁴ choices of four simple graphs inside {{0, 1, 2}}: "
            f"{ex.stats['n_hyp']:,} satisfy both hypotheses and {ex.stats['n_fail']:,} of "
            "those break the conclusion. Failures are common, not rare."),
        lean=("`#print axioms GraphCh10.supp28` lists only Lean's three standard axioms "
              "(propext, Classical.choice, Quot.sound), basic logical principles that almost "
              "every Lean proof relies on. There is no `sorry` (an unfinished step) and no "
              "axiom added by this project. Lean's kernel has checked every step shown above."),
    ),
]


def _step_titled(start: str) -> int:
    hits = [i for i, st in enumerate(STEPS) if st["title"].startswith(start)]
    assert len(hits) == 1, start
    return hits[0]


# Parts of the picture appear only once the walkthrough has explained them.
REVEAL = dict(
    unions=_step_titled("Union:"),                          # the union row
    iso=_step_titled("Isomorphism:"),                       # the ≅ signs and vertex maps
    verdict=_step_titled("The unions have different sizes"),  # ≅ / ≇ between the unions
    map=_step_titled("Try it:"),                            # the map tester
)


# ---------------------------------------------------------------------------
# 8. The interactive explorer
# ---------------------------------------------------------------------------

PANEL_ROWS = (("G₁", "H₁"), ("G₂", "H₂"), ("G₁ ∪ G₂", "H₁ ∪ H₂"))


class Explorer:
    """Interactive companion: the counterexample, relabelling H₂, a map tester, the proof."""

    MAX_CODE_LINES = 32

    def __init__(self, stats: dict):
        self.stats = stats
        self.lean = read_lean_sources()
        self._check_anchors()
        self.h2_pair = LEAN_H2_PAIR
        self.f: dict = {}
        self.map_idx = 0
        self.step = 0
        self.example_idx = 0
        self.message = ""
        self._conns: list = []

        for key in ("keymap.back", "keymap.forward"):  # free ← / → for the walkthrough
            plt.rcParams[key] = [k for k in plt.rcParams[key] if k not in ("left", "right")]

        self.fig = plt.figure(figsize=(18, 11.5), facecolor="white")
        try:
            self.fig.canvas.manager.set_window_title("Supp. 28: union and isomorphism")
        except AttributeError:
            pass
        self.fig.text(0.015, 0.972, "Supplementary Exercise 28:  if G₁ ≅ H₁ and G₂ ≅ H₂, "
                      "must G₁ ∪ G₂ ≅ H₁ ∪ H₂?", fontsize=18, fontweight="bold", color=COLOR_TEXT,
                      va="center")
        self.fig.text(0.015, 0.942, "An interactive companion to the Lean proof "
                      "GraphCh10.supp28 (a disproof). The pictures illustrate the "
                      "counterexample; Lean checks it.", fontsize=10.5, color=COLOR_WARN,
                      style="italic", va="center")
        self.caption = self.fig.text(0.015, 0.917, "", ha="left", va="top", fontsize=10,
                                     color=COLOR_TEXT, linespacing=1.35)

        # The six small pictures: rows (G₁ | H₁), (G₂ | H₂), (G₁ ∪ G₂ | H₁ ∪ H₂).
        self.ax_g: dict = {}
        self.rel_text, self.rel_sym = [], []
        for r, (left, right) in enumerate(PANEL_ROWS):
            y = 0.695 - r * 0.19
            self.ax_g[left] = self.fig.add_axes([0.035, y, 0.15, 0.145])
            self.ax_g[right] = self.fig.add_axes([0.315, y, 0.15, 0.145])
            self.rel_sym.append(self.fig.text(0.25, y + 0.09, "", ha="center", va="center",
                                              fontsize=20, color="#8A6A00", zorder=20,
                                              fontweight="bold"))
            self.rel_text.append(self.fig.text(0.25, y + 0.06, "", ha="center",
                                               va="top", fontsize=9.5, color="#8A6A00",
                                               fontweight="bold", linespacing=1.4, zorder=20,
                                               bbox=dict(boxstyle="round,pad=0.2", fc="white",
                                                         ec="none", alpha=0.9)))
        self.ax_legend = self.fig.add_axes([0.015, 0.268, 0.465, 0.035])
        self.ax_legend.axis("off")
        self.ax_legend.legend(*legend_entries(), loc="center", ncol=3, frameon=False,
                              fontsize=8.8, handlelength=2.0, columnspacing=1.0)

        def button(rect, label, cb, color="#F0F0F0", size=10):
            b = Button(self.fig.add_axes(rect), label, color=color, hovercolor="#DDE8F5")
            b.label.set_fontsize(size)
            b.on_clicked(cb)
            return b

        # Relabel H₂.
        self.ax_relabel = self.fig.add_axes([0.015, 0.025, 0.17, 0.235])
        self.ax_relabel.set_xticks([])
        self.ax_relabel.set_yticks([])
        self.ax_relabel.text(0.05, 0.94, "Relabel H₂ = K₂ on {a, b}", fontsize=10,
                             fontweight="bold", va="top", transform=self.ax_relabel.transAxes)
        self.ax_relabel.text(0.05, 0.83, "(G₂ ≅ H₂ holds for each)", fontsize=8.8,
                             va="top", color="#555555", transform=self.ax_relabel.transAxes)
        self.btn_pairs = {}
        for i, pair in enumerate(combinations(range(AMBIENT), 2)):
            x = 0.022 + (i % 2) * 0.08
            y = 0.155 - (i // 2) * 0.04
            self.btn_pairs[pair] = button([x, y, 0.075, 0.034], fmt_set(pair),
                                          lambda _e, p=pair: self.set_h2(p), size=9.5)
        self.btn_reset = button([0.022, 0.032, 0.155, 0.034], "Reset (Lean example)",
                                lambda _e: self.reset(), color="#E3EEDF", size=9.5)

        # Map tester.
        self.ax_map = self.fig.add_axes([0.195, 0.075, 0.285, 0.185])
        self.ax_map_box = self.fig.add_axes([0.19, 0.025, 0.295, 0.235], zorder=-1)
        self.ax_map_box.set_xticks([])
        self.ax_map_box.set_yticks([])
        self.btn_f = {}
        for i, v in enumerate((0, 1)):
            self.btn_f[v] = button([0.197 + i * 0.07, 0.032, 0.065, 0.034], f"f({v}) ▸",
                                   lambda _e, v=v: self.bump(v), size=9.5)
        self.btn_allmaps = button([0.337 + 0.005, 0.032, 0.135, 0.034], "Next map ▸",
                                  lambda _e: self.next_map(), size=9.5)

        # Explanation and code.
        self.ax_text = self.fig.add_axes([0.505, 0.615, 0.48, 0.305])
        self.ax_code = self.fig.add_axes([0.505, 0.105, 0.48, 0.5])
        for ax in (self.ax_text, self.ax_code):
            ax.axis("off")
        self.btn_prev = button([0.505, 0.035, 0.085, 0.055], "◀ Previous", lambda _e: self.go(-1),
                               size=10.5)
        self.btn_next = button([0.700, 0.035, 0.085, 0.055], "Next ▶", lambda _e: self.go(+1),
                               color="#E3EEDF", size=10.5)
        self.btn_example = button([0.795, 0.035, 0.09, 0.055], "Next example",
                                  lambda _e: self.next_example(), size=10.5)
        self.step_label = self.fig.text(0.6425, 0.0625, "", ha="center", va="center",
                                        fontsize=11, fontweight="bold", color=COLOR_TEXT)
        self.fig.text(0.985, 0.0625, "keys: ← / →", ha="right", va="center", fontsize=9.5,
                      color="#777777")

        self.fig.canvas.mpl_connect("key_press_event", self._on_key)
        self._reset_map()
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
    def G(self) -> dict[str, SG]:
        """The four graphs (G₁, G₂, H₁ from Lean; H₂ = K₂ on the current pair)."""
        return {**LEAN_GRAPHS, "H₂": k2(*self.h2_pair)}

    @property
    def unions(self) -> tuple[SG, SG]:
        g = self.G
        return union(g["G₁"], g["G₂"]), union(g["H₁"], g["H₂"])

    @property
    def f2(self) -> dict:
        """The isomorphism G₂ → H₂ that is drawn (v ↦ v + 2 for the Lean example)."""
        return iso_map(self.G["G₂"], self.G["H₂"])

    @property
    def is_lean_example(self) -> bool:
        return self.h2_pair == LEAN_H2_PAIR

    def _reset_map(self) -> None:
        UG, UH = self.unions
        self.map_list = list(all_maps(UG.V, UH.V))
        self.map_idx = 0
        self.f = dict(self.map_list[0])
        # start with the 'obvious' guess f(v) = v when it is possible
        if all(v in UH.V for v in UG.V):
            self.f = {v: v for v in UG.V}
            self.map_idx = self.map_list.index(self.f)

    def set_h2(self, pair: tuple[int, int]) -> None:
        self.h2_pair = pair
        self.message = f"H₂ relabelled to {fmt_set(pair)}"
        self._reset_map()
        self.redraw()

    def reset(self) -> None:
        self.h2_pair = LEAN_H2_PAIR
        self.message = ""
        self._reset_map()
        self.redraw()

    def bump(self, v: int) -> None:
        """Send v to the next vertex of V(H₁ ∪ H₂)."""
        cod = sorted(self.unions[1].V)
        if v not in self.f:
            return
        self.f = {**self.f, v: cod[(cod.index(self.f[v]) + 1) % len(cod)]}
        self.map_idx = self.map_list.index(self.f)
        self.redraw()

    def next_map(self) -> None:
        self.map_idx = (self.map_idx + 1) % len(self.map_list)
        self.f = dict(self.map_list[self.map_idx])
        self.redraw()

    def go(self, delta: int) -> None:
        self.enter_step(max(0, min(len(STEPS) - 1, self.step + delta)))

    def next_example(self) -> None:
        self.example_idx += 1
        self.redraw()

    def enter_step(self, k: int) -> None:
        self.step, self.example_idx = k, 0
        self.redraw()

    def _on_key(self, event) -> None:
        if event.key == "right":
            self.go(+1)
        elif event.key == "left":
            self.go(-1)

    # -- what to highlight --------------------------------------------------

    def focus_info(self, kind: str) -> tuple[dict, int]:
        """What the current step highlights. Returns (info, #examples 'Next example' cycles)."""
        g = self.G
        UG, UH = self.unions
        ident = {v: v for v in g["G₁"].V}
        early = self.step < REVEAL["verdict"]
        base = dict(gold=set(), arrows={}, inv_arrows={}, tags={}, edge_hl={}, f=self.f2,
                    pair_text="", map_gold=False, relabel_gold=False,
                    caption=f"G₂ ≅ H₂ by {fmt_map(self.f2)}.  "
                            f"{_sizes_sentence(self) if early else _union_sentence(self)}.")
        if kind == "simple":
            G = g["G₁"]
            return dict(base, gold={"G₁"}, caption=f"G₁ = {LEAN_NAMES['G₁']}:  {fmt_graph(G)}. "
                        "Dashed grey circles: labels of Fin 4 that are not vertices of G₁."), 1
        if kind == "unions":
            return dict(base, gold={"G₁ ∪ G₂", "H₁ ∪ H₂"},
                        caption=f"G₁ ∪ G₂: {fmt_graph(UG)}.   H₁ ∪ H₂: {fmt_graph(UH)}."), 1
        if kind == "iso1":
            return dict(base, gold={"G₁", "H₁"}, arrows={0: ident},
                        caption=f"G₁ ≅ H₁ by the identity {fmt_map(ident)}: the same graph."), 1
        if kind == "iso2":
            G, H, f = g["G₂"], g["H₂"], self.f2
            # start with a real edge (0, 1), then (1, 0), then the loop pairs
            pairs = sorted(product(sorted(G.V), repeat=2), key=lambda q: (q[0] == q[1], q))
            k = self.example_idx % len(pairs)
            a, b = pairs[k]
            lhs, rhs = s_(f[a], f[b]) in H.E, s_(a, b) in G.E
            yn = {True: "yes", False: "no"}

            def name(x, y):
                return f"{{{x}, {y}}}" + (" (a loop: never an edge)" if x == y else "")
            text = (f"Pair {k + 1} of {len(pairs)}: v₁ = {a}, v₂ = {b}. Is {name(f[a], f[b])} "
                    f"an edge of H₂? {yn[lhs]}. Is {name(a, b)} an edge of G₂? {yn[rhs]}. "
                    f"{'Both answers agree ✓' if lhs == rhs else 'The answers differ ✗'}.")
            tags_g = {a: "v₁ = v₂"} if a == b else {a: "v₁", b: "v₂"}
            tags_h = {f[a]: "f(v₁) = f(v₂)"} if a == b else {f[a]: "f(v₁)", f[b]: "f(v₂)"}
            return dict(base, gold={"G₂", "H₂"}, arrows={1: f}, pair_text=text,
                        tags={"G₂": tags_g, "H₂": tags_h},
                        edge_hl={"G₂": {s_(a, b)} & G.E, "H₂": {s_(f[a], f[b])} & H.E},
                        caption=f"G₂ ≅ H₂ by f: {fmt_map(f)}.   v₁ = {a}, v₂ = {b}:  "
                                f"{{f(v₁), f(v₂)}} ∈ E(H₂)? {yn[lhs]};  {{v₁, v₂}} ∈ E(G₂)? "
                                f"{yn[rhs]}  ({k + 1} of {len(pairs)})"), len(pairs)
        if kind == "bij":
            f = self.f2
            inv = {w: v for v, w in f.items()}
            return dict(base, gold={"G₂", "H₂"}, arrows={1: f}, inv_arrows={1: inv},
                        caption=f"The bijection f: {fmt_map(f)} (gold dashed arrows);  its "
                                f"inverse: {fmt_map(inv)} (blue dotted arrows)."), 1
        if kind == "four":
            return dict(base, gold={"G₁", "G₂", "H₁", "H₂"}, arrows={0: ident, 1: self.f2},
                        caption=f"G₁ = G₂ = H₁ = K₂ on {{0, 1}},  H₂ = K₂ on "
                                f"{fmt_set(self.h2_pair)}.  G₁ ≅ H₁ (identity), G₂ ≅ H₂ "
                                f"({fmt_map(self.f2)})."), 1
        if kind == "statement":
            return dict(base, gold={"G₁", "G₂", "H₁", "H₂", "G₁ ∪ G₂", "H₁ ∪ H₂"},
                        arrows={0: ident, 1: self.f2}), 1
        if kind == "relabel":
            return dict(base, gold={"H₂", "H₁ ∪ H₂"}, relabel_gold=True, map_gold=True,
                        arrows={1: self.f2}), 1
        if kind == "map":
            return dict(base, gold={"G₁ ∪ G₂", "H₁ ∪ H₂"}, map_gold=True,
                        caption=f"V(G₁ ∪ G₂) = {fmt_set(UG.V)} ({len(UG.V)} vertices),  "
                                f"V(H₁ ∪ H₂) = {fmt_set(UH.V)} ({len(UH.V)} vertices).  "
                                f"Trying f: {fmt_map(self.f)}."), 1
        if kind == "all":
            return dict(base, arrows={0: ident, 1: self.f2}), 1
        raise ValueError(kind)

    # -- drawing ------------------------------------------------------------

    def redraw(self) -> None:
        s = STEPS[self.step]
        focus, n_examples = self.focus_info(s["focus"])
        self._draw_graphs(focus)
        self._draw_controls(focus)
        self._draw_text(s, focus)
        self._draw_code(s)
        last = len(STEPS) - 1
        self.step_label.set_text(f"Page {self.step + 1} / {len(STEPS)}"
                                 + ("  (end)" if self.step == last else ""))
        for b, off, on_color in ((self.btn_prev, self.step == 0, "#F0F0F0"),
                                 (self.btn_next, self.step == last, "#E3EEDF")):
            b.label.set_alpha(0.3 if off else 1.0)
            b.color = "#F7F7F7" if off else on_color
            b.ax.set_facecolor(b.color)
        self.btn_example.ax.set_visible(n_examples > 1)
        self.fig.canvas.draw_idle()

    def _draw_graphs(self, focus: dict) -> None:
        g = self.G
        UG, UH = self.unions
        for c in self._conns:
            c.remove()
        self._conns = []
        pictures = {
            "G₁": (g["G₁"], [(g["G₁"], COLOR_ONE)]), "H₁": (g["H₁"], [(g["H₁"], COLOR_ONE)]),
            "G₂": (g["G₂"], [(g["G₂"], COLOR_TWO)]), "H₂": (g["H₂"], [(g["H₂"], COLOR_TWO)]),
            "G₁ ∪ G₂": (UG, [(g["G₁"], COLOR_ONE), (g["G₂"], COLOR_TWO)]),
            "H₁ ∪ H₂": (UH, [(g["H₁"], COLOR_ONE), (g["H₂"], COLOR_TWO)]),
        }
        show_unions = self.step >= REVEAL["unions"]
        show_iso = self.step >= REVEAL["iso"]
        show_verdict = self.step >= REVEAL["verdict"]
        self.shown = dict(unions=show_unions, iso=show_iso, verdict=show_verdict,
                          map=self.step >= REVEAL["map"])
        for key, (G, parts) in pictures.items():
            ax = self.ax_g[key]
            ax.clear()
            if key in PANEL_ROWS[2] and not show_unions:  # not explained yet
                frame(ax)
                style_box(ax, False)
                ax.set_facecolor("#F2F2F2")
                ax.text(0, 0, f"{key}\n(explained in step {REVEAL['unions'] + 1})",
                        ha="center", va="center", fontsize=10, color="#888888")
                ax.set_title(key, fontsize=10, pad=3, color="#888888")
                continue
            draw_sg(ax, G, parts=parts, tags=focus["tags"].get(key),
                    edge_hl=focus["edge_hl"].get(key), fontsize=11)
            frame(ax)
            style_box(ax, key in focus["gold"])
            lean = LEAN_NAMES.get(key)
            if key == "H₂" and not self.is_lean_example:
                lean = "relabelled"
            head = f"{key}" + (f"  ({lean})" if lean else "")
            ax.set_title(f"{head}\n{fmt_graph(G)}", fontsize=10, pad=3,
                         fontweight="bold" if key in focus["gold"] else "normal")
        paths: dict[int, list] = {0: [], 1: [], 2: []}
        # inverse arrows run right-to-left, so their bend is flipped (and made larger) to keep
        # them outside the forward arrows and away from the middle label
        for arrows, color, ls, rev, bend in (
                (focus["arrows"], "#8A6A00", (0, (4, 2)), False, 1.0),
                (focus["inv_arrows"], COLOR_VERTEX, (0, (1, 2)), True, -1.4)):
            for row, f in arrows.items():
                left, right = PANEL_ROWS[row]
                axA, axB = self.ax_g[left], self.ax_g[right]
                if rev:
                    axA, axB = axB, axA
                self._conns += map_arrows(self.fig, axA, axB, f, color=color, linestyle=ls,
                                          bend=bend)
                paths[row] += [arrow_points(self.fig, axA, axB, v, w, bend=bend)
                               for v, w in f.items()]
        iso1 = isomorphic(g["G₁"], g["H₁"])
        iso2 = isomorphic(g["G₂"], g["H₂"])
        isoU = isomorphic(UG, UH)
        shift = self.f2 == shift_map(g["G₂"])
        self.rel_sym[0].set_text(("≅" if iso1 else "≇") if show_iso else "")
        self.rel_sym[1].set_text(("≅" if iso2 else "≇") if show_iso else "")
        self.rel_text[0].set_text("identity: 0↦0, 1↦1" if show_iso else "")
        self.rel_text[1].set_text(((f"v ↦ v + {SHIFT_K}: " if shift else "")
                                   + fmt_map(self.f2)) if show_iso else "")
        if show_verdict:
            self.rel_sym[2].set_text("≅" if isoU else "≇")
            self.rel_text[2].set_text(f"{len(UG.V)} vs {len(UH.V)} vertices")
            col = COLOR_OK if isoU else COLOR_WARN
        else:  # the answer is not given away before it is explained
            self.rel_sym[2].set_text("≅ ?" if show_iso and show_unions else "")
            self.rel_text[2].set_text("the question" if show_iso and show_unions else "")
            col = "#8A6A00"
        for t in (self.rel_text[2], self.rel_sym[2]):
            t.set_color(col)
        self.rel_clearance = {r: self._place_label(r, paths[r]) for r in range(3)}
        head = "" if self.is_lean_example else f"[{self.message}]  "
        self.caption.set_text(textwrap.fill(head + focus["caption"], 112))

    REL_HALF = 0.023  # half the height of the ≅ sign + one-line label block (figure units)

    def _place_label(self, row: int, paths: list) -> float:
        """Put the ≅ sign and its label in the middle column where no map arrow passes.
        Returns the clearance (figure units) between the block and the nearest arrow."""
        y0 = 0.695 - row * 0.19
        pts = [py for path in paths for px, py in path if 0.2 <= px <= 0.3]
        best_c, best = y0 + 0.0725, float("inf")
        if pts:
            cands = [y0 + 0.025 + 0.0025 * i for i in range(55)]  # may rise above the boxes
            scored = [(min(abs(py - c) for py in pts) - self.REL_HALF, -abs(c - y0 - 0.0725), c)
                      for c in cands]
            best, _tie, best_c = max(scored)
        self.rel_sym[row].set_position((0.25, best_c + 0.009))
        self.rel_text[row].set_position((0.25, best_c - 0.004))
        return best

    def _draw_controls(self, focus: dict) -> None:
        style_box(self.ax_relabel, focus["relabel_gold"])
        style_box(self.ax_map_box, focus["map_gold"])
        for pair, b in self.btn_pairs.items():
            on = pair == self.h2_pair
            b.color = "#FFE08A" if on else "#F0F0F0"
            b.ax.set_facecolor(b.color)
            b.label.set_fontweight("bold" if on else "normal")
        UG, UH = self.unions
        show = self.shown["map"]
        for b in (*self.btn_f.values(), self.btn_allmaps):
            b.ax.set_visible(show)
        if not show:  # the map tester is introduced in the 'Try it' step
            self.verdict = map_verdict(UG, UH, self.f)
            ax = self.ax_map
            ax.clear()
            ax.axis("off")
            ax.text(0.5, 0.5, f"Map tester\n(opens in step {REVEAL['map'] + 1}, 'Try it')",
                    ha="center", va="center", fontsize=10, color="#888888")
            self.ax_map_box.set_facecolor("#F2F2F2")
            return
        self.verdict = draw_map(self.ax_map, UG, UH, self.f, fs=9,
                                title=f"Try a map f : V(G₁ ∪ G₂) → V(H₁ ∪ H₂)   "
                                      f"(map {self.map_idx + 1} of {len(self.map_list)})")

    def _draw_text(self, s: dict, focus: dict) -> None:
        ax = self.ax_text
        ax.clear()
        ax.axis("off")
        math_txt = s["math"](self, focus)
        if not self.is_lean_example:
            math_txt = RELABELLED.format(fmt_set(self.h2_pair), fmt_set(LEAN_H2_PAIR)) + math_txt
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

def _press(fig, ax, x: float, y: float) -> None:
    """Simulate a left mouse click at (x, y) in axes fraction."""
    fig.canvas.draw()
    tx, ty = ax.transAxes.transform((x, y))
    for name in ("button_press_event", "button_release_event"):
        fig.canvas.callbacks.process(name, MouseEvent(name, fig.canvas, tx, ty, button=1))


def _click(ex: Explorer, btn: Button) -> None:
    _press(ex.fig, btn.ax, 0.5, 0.5)


def _key(ex: Explorer, key: str) -> None:
    ex.fig.canvas.callbacks.process("key_press_event",
                                    KeyEvent("key_press_event", ex.fig.canvas, key))


def _check_layout(ex: Explorer) -> None:
    """No text in the explanation, code or map panel runs past its bottom or right edge."""
    ex.fig.canvas.draw()
    renderer = ex.fig.canvas.get_renderer()
    for ax in (ex.ax_text, ex.ax_code, ex.ax_map):
        box = ax.get_window_extent(renderer)
        if ax is ex.ax_map:
            box = ex.ax_map_box.get_window_extent(renderer)
        for t in ax.texts:
            if not t.get_text().strip():
                continue
            bb = t.get_window_extent(renderer)
            assert bb.y0 >= box.y0 - 2 and bb.x1 <= box.x1 + 2, \
                f"text overflows its panel: {t.get_text()[:60]!r}"
    # the caption above the pictures must not run into the first row's titles
    cap = ex.caption.get_window_extent(renderer)
    top = max(ex.ax_g[k].title.get_window_extent(renderer).y1 for k in PANEL_ROWS[0])
    assert cap.y0 >= top - 1, "caption overlaps the picture titles"
    assert cap.x1 <= ex.fig.bbox.width * 0.5, "caption runs into the right half"
    # the ≅ sign and its label sit clear of every map arrow
    assert min(ex.rel_clearance.values()) > 0, f"label crosses an arrow: {ex.rel_clearance} (step {ex.step + 1}, H₂ on {ex.h2_pair})"


def self_test(ex: Explorer, outdir: Path) -> None:
    outdir.mkdir(parents=True, exist_ok=True)
    # 1. Every step renders for every example it offers, and its text and code fit.
    for k, s in enumerate(STEPS):
        ex.enter_step(k)
        _f, n = ex.focus_info(s["focus"])
        for _ in range(max(n, 1)):
            ex.redraw()
            _check_layout(ex)
            ex.next_example()
        ex.enter_step(k)
        a, b = ex.code_window(s)
        assert all(a <= i < b for i in ex.highlighted(s)), f"step {k + 1}: highlight off-screen"
        assert ex.highlighted(s) or s["focus"] == "all", f"step {k + 1}: no code highlighted"
        ex.fig.savefig(outdir / f"step_{k + 1:02d}.png", dpi=110)
    # 2. Next / Previous buttons and the arrow keys.
    ex.enter_step(0)
    _click(ex, ex.btn_next)
    assert ex.step == 1, "Next button did not advance"
    _click(ex, ex.btn_prev)
    assert ex.step == 0, "Previous button did not go back"
    _click(ex, ex.btn_prev)
    assert ex.step == 0, "Previous on step 1 must stay on step 1"
    _key(ex, "right")
    assert ex.step == 1, "→ key did not advance"
    _key(ex, "left")
    assert ex.step == 0, "← key did not go back"
    ex.enter_step(len(STEPS) - 1)
    _click(ex, ex.btn_next)
    assert ex.step == len(STEPS) - 1, "Next on the last step must stay there"
    # 3. 'Next example' cycles the four pairs in the edge-condition steps, and each agrees.
    k_iso = next(i for i, s in enumerate(STEPS) if s["focus"] == "iso2")
    ex.enter_step(k_iso)
    assert ex.btn_example.ax.get_visible()
    seen = set()
    for _ in range(4):
        f, n = ex.focus_info("iso2")
        assert n == 4 and "agree ✓" in f["pair_text"]
        seen.add(f["pair_text"])
        _click(ex, ex.btn_example)
    assert len(seen) == 4
    f, _n = ex.focus_info("iso2")
    assert "v₁ = 0, v₂ = 1" in f["pair_text"], "edge examples must start at the pair (0, 1)"
    ex.enter_step(0)
    assert not ex.btn_example.ax.get_visible()
    # 3b. Nothing is shown before it is taught.
    assert not any(ex.shown.values()) and all(t.get_text() == "" for t in ex.rel_sym)
    assert not ex.btn_allmaps.ax.get_visible() and not ex.btn_f[0].ax.get_visible()
    ex.enter_step(REVEAL["iso"])
    assert ex.rel_sym[2].get_text() == "≅ ?", "the union verdict is given away too early"
    ex.enter_step(REVEAL["verdict"])
    assert ex.rel_sym[2].get_text() == "≇"
    ex.enter_step(REVEAL["map"])
    assert ex.btn_allmaps.ax.get_visible()
    # 3c. The step that builds the bijection shows only f and its inverse, no pair tags.
    k_bij = next(i for i, s in enumerate(STEPS) if s["focus"] == "bij")
    ex.enter_step(k_bij)
    f, n = ex.focus_info("bij")
    assert n == 1 and not f["tags"] and not ex.btn_example.ax.get_visible()
    assert f["inv_arrows"] == {1: {2: 0, 3: 1}}
    # 4. The map tester on the Lean example: no map is a bijection, let alone an isomorphism.
    k_map = next(i for i, s in enumerate(STEPS) if s["focus"] == "map")
    ex.enter_step(k_map)
    assert ex.f == {0: 0, 1: 1} and not ex.verdict["onto"] and ex.verdict["missed"] == [2, 3]
    ex.fig.savefig(outdir / "map_identity_guess.png", dpi=110)
    _click(ex, ex.btn_f[1])
    assert ex.f == {0: 0, 1: 2}
    _click(ex, ex.btn_f[0])
    _click(ex, ex.btn_f[0])
    assert ex.f == {0: 2, 1: 2} and not ex.verdict["inj"]
    ex.fig.savefig(outdir / "map_collision.png", dpi=110)
    for _ in range(len(ex.map_list)):
        _click(ex, ex.btn_allmaps)
        assert not ex.verdict["onto"] and not ex.verdict["iso"]
    assert len(ex.map_list) == 16
    # 5. Relabelling H₂: G₂ ≅ H₂ always; the unions are isomorphic only for {0, 1}.
    k_rel = next(i for i, s in enumerate(STEPS) if s["focus"] == "relabel")
    ex.enter_step(k_rel)
    for pair, b in ex.btn_pairs.items():
        _click(ex, b)
        assert ex.h2_pair == pair
        g = ex.G
        assert is_isomorphism(g["G₂"], g["H₂"], ex.f2)
        UG, UH = ex.unions
        assert isomorphic(UG, UH) == (pair == (0, 1))
        for k in range(len(STEPS)):  # every step still renders, with the warning
            ex.enter_step(k)
            _check_layout(ex)
        ex.enter_step(k_rel)
        ex.fig.savefig(outdir / f"relabel_{pair[0]}{pair[1]}.png", dpi=110)
    # ... with H₂ on {0, 1}, some map IS an isomorphism, and 'Next map' finds it.
    _click(ex, ex.btn_pairs[(0, 1)])
    ex.enter_step(k_map)
    found = []
    for _ in range(len(ex.map_list)):
        if ex.verdict["iso"]:
            found.append(dict(ex.f))
        _click(ex, ex.btn_allmaps)
    assert found == [{0: 0, 1: 1}, {0: 1, 1: 0}], found
    ex.f, ex.map_idx = {0: 1, 1: 0}, ex.map_list.index({0: 1, 1: 0})
    ex.redraw()
    ex.fig.savefig(outdir / "relabel_01_isomorphism.png", dpi=110)
    # ... and the counting sentences of steps 8, 15, 19 describe the CURRENT unions.
    k_card = _step_titled("Helper: isomorphic ⇒")
    k_hcard = _step_titled("hcard:")
    for k in (k_rel, k_card, k_hcard):
        ex.enter_step(k)
        txt = STEPS[k]["math"](ex, ex.focus_info(STEPS[k]["focus"])[0])
        assert "both unions have 2 vertices" in txt and "4 different dots" not in txt, k
    ex.enter_step(k_card)
    ex.fig.savefig(outdir / "step_15_relabel_01.png", dpi=110)
    _click(ex, ex.btn_reset)
    for k in (k_rel, k_card, k_hcard):
        ex.enter_step(k)
        txt = STEPS[k]["math"](ex, ex.focus_info(STEPS[k]["focus"])[0])
        assert "2 arrows cannot reach 4 different dots" in txt, k
    # 6. Reset returns to the Lean counterexample.
    _click(ex, ex.btn_reset)
    assert ex.is_lean_example and ex.f == {0: 0, 1: 1}
    print(f"Explorer self-test passed: {len(STEPS)} steps rendered (every example, text and "
          f"code fit), buttons, keys, relabelling, map tester and reset work; snapshots in "
          f"{outdir}")


# ---------------------------------------------------------------------------
# 10. Entry point
# ---------------------------------------------------------------------------

def main() -> None:
    try:
        sys.stdout.reconfigure(encoding="utf-8")  # so ≅, ∪ print on Windows consoles
    except (AttributeError, ValueError):
        pass
    parser = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    parser.add_argument("--static", action="store_true",
                        help="only run the checks and save the PNG (no window)")
    parser.add_argument("--snapshots", metavar="DIR", type=Path,
                        help="headless self-test of the explorer; save one PNG per step")
    args = parser.parse_args()

    stats = run_checks()
    G1, G2, H1, H2 = (LEAN_GRAPHS[r] for r in ROLES)
    for r in ROLES:
        print(f"{r} = {LEAN_NAMES[r]}: {fmt_graph(LEAN_GRAPHS[r])}")
    print(f"G₁ ∪ G₂: {fmt_graph(union(G1, G2))}")
    print(f"H₁ ∪ H₂: {fmt_graph(union(H1, H2))}")
    c = stats["counts"]
    print(f"Maps V(G₁ ∪ G₂) → V(H₁ ∪ H₂): {c['total']} in all, {c['inj']} one-to-one, "
          f"{c['onto']} onto, {c['iso']} isomorphisms")
    print(f"All assertions passed (approved statement, parsed graphs, both hypotheses, union "
          f"vertex sets, no bijection, relabellings, {stats['n_graphs3']}⁴ quadruples inside "
          f"{{0, 1, 2}}: {stats['n_hyp']:,} satisfy the hypotheses, {stats['n_fail']:,} "
          f"break the conclusion).")

    out = Path(__file__).resolve().parent / "supp28.png"
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
