# GraphCh10

Computer-checked solutions to selected exercises from **Chapter 10 (Graphs)** of
*Discrete Mathematics and Its Applications* by Kenneth H. Rosen, written in the
[Lean 4](https://lean-lang.org/) proof assistant, plus interactive Python visualizations that
explain each proof.

---

## What is this project? (no background needed)

### A 30-second intro to graph theory

A **graph** is a set of dots (**vertices**) joined by lines (**edges**). Think of cities and
roads, people and friendships, or web pages and links.

- An edge from a vertex back to itself is a **loop**.
- Two or more edges joining the same pair of vertices are **multiple (parallel) edges**.
- A **simple graph** has no loops and no multiple edges.
- The **degree** of a vertex is how many edges touch it (a loop counts twice).
- In a **directed graph** every edge has an arrow (a one-way street). A vertex's
  **in-degree** / **out-degree** counts arrows coming in / going out.

### A 30-second intro to Lean

Lean is a programming language in which you can write mathematical statements *and their
proofs*. When Lean "compiles" a file, it checks every logical step of every proof. If the
project builds without errors, the theorems are correct — no human has to re-check the
reasoning. A proof that is unfinished is marked with the keyword `sorry`, and Lean warns about it.

### What this repository does

For each exercise it:

1. **Defines** the graph concepts it needs (graph, degree, neighbourhood, path, …), taken
   only from the chapter's definitions sheet in `docs/`.
2. **States** the exercise as a Lean theorem, faithfully translating the book's wording.
3. **Proves** it, with the proof laid out like a paper proof (named steps, each with a
   plain-English comment).
4. Ships a **visualization** (`visualizations/suppNN.py`) that draws the graphs involved and
   walks through the Lean proof step by step.

The project deliberately does **not** use Mathlib's built-in graph theory library — every
graph notion is built from scratch in `GraphCh10/Definitions.lean`, so the formalization
matches the textbook exactly. Only a small, explicitly listed set of basic Mathlib modules
(finite sets, counting, etc.) is allowed; see `allowed-imports.txt`.

### Exercises formalized so far

All are **complete** (fully proved, no `sorry`, no extra axioms).

| Exercise | Book problem (paraphrased) | Result | Lean file |
|---|---|---|---|
| Supp. 8 | Does every finite multigraph with ≥ 2 vertices have two vertices of the same degree? | **False** — counterexample with degrees 1, 3, 2 | `GraphCh10/Exercises/Supp08.lean` |
| Supp. 9(a) | Show N(A ∪ B) = N(A) ∪ N(B) (neighbourhoods of vertex sets) | Proved | `GraphCh10/Exercises/Supp09a.lean` |
| Supp. 10(b) | Show \|N(v)\| = deg v for every vertex ⇔ G is simple | Proved | `GraphCh10/Exercises/Supp10b.lean` |
| Supp. 28 | If G₁ ≅ H₁ and G₂ ≅ H₂, must G₁ ∪ G₂ ≅ H₁ ∪ H₂? | **False** — counterexample | `GraphCh10/Exercises/Supp28.lean` |
| Supp. 39 | A graph with a cut edge is not orientable | Proved | `GraphCh10/Exercises/Supp39.lean` |
| Supp. 41 | In a tournament, what is in-degree + out-degree of a vertex? | **n − 1** (n = number of vertices) | `GraphCh10/Exercises/Supp41.lean` |

---

## Repository layout

```
GraphCh10/
├── GraphCh10.lean              Root file: imports everything, so building it checks the whole project
├── GraphCh10/
│   ├── Foundations.lean        The ONLY file that imports Mathlib (allowlisted modules only)
│   ├── Definitions.lean        All graph definitions, each quoting its source in docs/
│   ├── DefinitionTests.lean    Small example graphs that sanity-check the definitions
│   ├── Lemmas.lean             Reusable helper facts (e.g. "paths can be reversed")
│   ├── Exercises/SuppNN.lean   One exercise per file; first line is its status
│   └── Verification/VerifyNN.lean  Prints each theorem and the axioms it depends on
├── visualizations/suppNN.py    Interactive explainer for each exercise (+ a static .png)
├── docs/                       The definitions sheet and exercise sheet (the only sources used)
├── check.ps1                   Audit script enforcing the project's rules
├── allowed-imports.txt         Mathlib modules that may be imported
├── approved-axioms.txt         Axioms approved for use (currently none)
├── lakefile.toml               Lean build configuration (depends on Mathlib)
└── lean-toolchain              Exact Lean version (v4.34.1)
```

---

## Running it locally

### 1. Install Lean (via `elan`)

`elan` is Lean's version manager — it reads `lean-toolchain` and automatically installs the
exact Lean version this project needs. It also installs `lake`, Lean's build tool.

- **Windows (PowerShell):**
  ```powershell
  curl -O --location https://elan.lean-lang.org/elan-init.ps1
  powershell -ExecutionPolicy Bypass -f elan-init.ps1
  del elan-init.ps1
  ```
- **macOS / Linux:**
  ```bash
  curl https://elan.lean-lang.org/elan-init.sh -sSf | sh
  ```

Close and reopen your terminal afterwards, then check: `lake --version`.

You also need **git**. Optionally install **VS Code** with the **Lean 4** extension to read the
proofs interactively (hover over a step to see what remains to be proved).

### 2. Get the code

```bash
git clone <this-repository-url> GraphCh10
cd GraphCh10
```

### 3. Download the prebuilt Mathlib

Mathlib is large; compiling it from source takes hours. Download the precompiled version instead:

```bash
lake exe cache get
```

(The first run also downloads Lean itself and Mathlib's source — expect a few GB and several
minutes.)

### 4. Build = check every proof

```bash
lake build
```

If this finishes without errors, Lean has verified every definition, test and theorem in the
project. Warnings mentioning `sorry` would indicate an unfinished proof (there are none at present).

### 5. (Optional) See what a theorem depends on

```bash
lake env lean GraphCh10/Verification/Verify41.lean
```

This prints the theorem `supp41` and its axioms. Expect only Lean's standard axioms
(`propext`, `Classical.choice`, `Quot.sound`) or none at all — nothing project-specific.

### 6. (Optional, Windows) Run the rule audit

```powershell
.\check.ps1          # development checks
.\check.ps1 -Final   # strict: also fails on any unfinished exercise or `sorry`
```

It checks that only allowlisted modules are imported, that no Mathlib graph library or proof
shortcuts are used, that there are no unapproved axioms, and that every exercise file has a valid
status line. It ends with `ALL CHECKS PASSED` or `AUDIT FAILED`. (If PowerShell blocks the
script, run `powershell -ExecutionPolicy Bypass -File .\check.ps1`.)

---

## Interactive visualizations

Each exercise has a Python companion that draws the graphs, lets you click and edit them, and
steps through the Lean proof with Previous/Next buttons, explaining both the math and the Lean
code (which it reads from the project files, so it always matches).

**Requirements:** Python 3 with `networkx` and `matplotlib`. Run from the project root:

```bash
python -m pip install networkx matplotlib
python visualizations/supp08.py            # saves visualizations/supp08.png, then opens the window
python visualizations/supp08.py --static   # only runs its checks and saves the PNG (no window)
```

On Windows you can use `py` instead of `python`, e.g. `py visualizations\supp41.py`.
Replace `supp08` with any of: `supp08`, `supp09a`, `supp10b`, `supp28`, `supp39`, `supp41`.
The `.png` files in `visualizations/` are static previews if you just want a quick look.

---

## Troubleshooting

- **`lake build` starts compiling thousands of Mathlib files** — you skipped
  `lake exe cache get`. Stop it (Ctrl+C) and run that first.
- **`lake: command not found`** — reopen the terminal after installing `elan`, or make sure
  `~/.elan/bin` is on your `PATH`.
- **Visualization window doesn't appear** — you may be on a headless machine; use `--static`
  and open the generated `.png`.

## Source

Kenneth H. Rosen, *Discrete Mathematics and Its Applications*, Chapter 10. The definitions and
problems used are in `docs/Chapter_10_Results_Clean_v2.pdf` and
`docs/Chapter_10_Exercises_Clean.pdf`.
