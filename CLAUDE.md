# Rosen Ch. 10 (Graphs) in Lean 4

##  ONLY ALLOWED SOURCES (NO EXTERNAL SOURCES ALLOWED)
- docs/Chapter_10_Results_Clean_v2.pdf: the ONLY graph definitions and results.
- docs/Chapter_10_Exercises_Clean.pdf: the problems. A problem may name an
  extra theorem (e.g. Supp. 49 names Dirac); that theorem is then allowed,
  but only after I approve it as an axiom.
- Mathlib modules EXPLICITLY listed in `allowed-imports.txt`. Additional modules, including tactics, require approval before use. No Mathlib graph-theory definitions or theorems may be used, regardless of how they become accessible through imports

## SOURCE RULES
1. Only GraphCh10/Foundations.lean imports Mathlib, and only allowlisted modules.
   Every other file imports project files only.
2. Never use, search for, or read anything from Mathlib.Combinatorics
   (SimpleGraph, Digraph, Walk, matchings, colorings, Hall). Do not use web
   search or outside proofs. If a needed module is not on the allowlist, STOP
   and ask me; I edit the list.
3. Every graph notion must be defined in GraphCh10/Definitions.lean, using only the Results PDF or definitions explicitly provided in the Exercises PDF. Each definition must include a docstring identifying its source and quoting the relevant mathematical definition. If neither PDF defines a necessary concept, STOP and request approval before introducing it.
4. Sheet results we do not prove live in GraphCh10/Results.lean as `axiom`s,
   each with a docstring quoting the sheet. You may PROPOSE an axiom, never add
   one without my approval. No other axioms. No native_decide.
   Approved axioms are listed by name in `approved-axioms.txt`, which only I edit.
5. Never change a definition or a theorem statement to make a proof easier.
   If a statement looks wrong, stop and tell me.
6. Run `.\check.ps1` in development mode during construction, `.\check.ps1 -Final` before final acceptance, and `lake build` after relevant changes.

## MANDATORY PROOF STYLE: READABILITY OVER SHORT
7. Structure each proof like the paper proof: named `have` steps, each with a
   one-line comment saying what it establishes in plain English.
8. Introduce a helper lemma when it states a reusable mathematical fact (e.g.
   "an isomorphism maps paths to paths") or when it makes a step easier to
   check on its own. Shared lemmas go in GraphCh10/Lemmas.lean with a docstring.
9. Prefer `calc`, `rw` and `simp only [...]` on steps that carry the math.
   Automation (`simp`, `omega`, `decide`, `aesop`) is fine for routine
   bookkeeping. Never golf; there is no line limit. If a proof passes about
   40 lines, ask whether a lemma would make it clearer.
10. Every theorem uses `:= by`.

## REQUIRED LAYOUT
11. One exercise per file: GraphCh10/Exercises/Supp08.lean, Review03.lean, ...
    Theorem names: supp08, supp09a, review03. Docstring = the book's problem text.
12. During statement formalization, sorry is permitted ONLY when an exercise is designated UNFINISHED. When an exercise is marked complete, its proof and all dependencies must be free of sorry and unapproved axioms. The final project MUST contain NO sorry.
13. For "prove or disprove" or "find" problems: tell me the answer and why BEFORE writing Lean.
14. Before attempting any proof, present the Lean theorem statement alongside a precise English translation. Preserve ALL original hypotheses, quantifiers, and conclusions. Do NOT strengthen assumptions, weaken conclusions, or replace an exercise with a special case without explicit approval. Classify partial formalizations separately from complete solutions.
15. The first line of every exercise file is its status: `-- STATUS: UNFINISHED`,
    `-- STATUS: PARTIAL` (an approved special case, fully proved) or
    `-- STATUS: COMPLETE`. New files start UNFINISHED. Only I change a status to
    PARTIAL or COMPLETE; when you think one is ready, tell me. Exercise files never
    import other exercise files.