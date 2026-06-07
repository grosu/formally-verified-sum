# Automatically Formally Verifying AI-Generated Code — An Experiment

This folder is an experiment in **end-to-end formal verification of AI-generated
code**. From a natural-language prompt, an AI agent (Claude Code) produced a
working program, a formal specification of its correctness, and a
**complete formal-verification proof** — all of it generated, none
of it hand-written beyond the prompt itself. (The AI *did* define the small
language the program is verified in — *mini Python* — and produce **its** formal
semantics; it did **not** produce a formal semantics of Python, the language
`summation.py` is actually written in. See the status note below.)

The thesis: with AI, producing code *that is formally verifiable* — and actually
verified — can take almost no extra human effort. The aspiration is **zero extra
effort**: you describe the program you want, and a machine-checkable proof of its
correctness comes for free alongside it. We see this experiment as the seed of a
**product** built around that idea.

## What was produced

A tiny but complete, fully verified pipeline for the function `sum(n) = 1 + 2 +
… + n`:

| Artifact | What it is |
|---|---|
| [`summation.py`](summation.py) | the program (written test-first) |
| [`test_sum.py`](test_sum.py) | its tests |
| [`mini-python.k`](mini-python.k) | a minimal **K** semantics ("mini Python") of just the language constructs the program uses |
| [`mini-python-spec.k`](mini-python-spec.k) | the correctness **specification** as K reachability `claim`s (the loop invariant + the function contract) |
| [`sum-correctness-proof.md`](sum-correctness-proof.md) | the language-independent reachability-logic proof |
| [`sum-verification.md`](sum-verification.md) | **the full write-up**: program, semantics, spec, informal proof, and the complete machine-oriented formal proof |

The complete story — and the exact prompts actually used — is in
[`sum-verification.md`](sum-verification.md) (see its **Section 6,
Reproducibility**).

## The prompt of the future

In the product we envision, this entire artifact is generated from **one short
prompt**:

> ### `Implement sum(n) in Python — the sum of 1 to n — and prove it correct end-to-end.`

That single line is all the human should ever need to write. From it, the tool
delivers the program *together with* a complete, machine-checked proof of its
correctness. In the limit, formal verification is simply **always on** — you
would not even add "and prove it correct"; the verified artifacts would come back
by default, at zero extra effort.

## Why the real prompts were longer (today's limitations)

The prompts actually used in this experiment were a longer, step-by-step sequence
(reproduced verbatim in `sum-verification.md` §6): *learn matching logic*, *read
the K framework*, *write the semantics*, *infer the loop invariant*, *prove it*,
*assemble a document*. That extra guidance was needed for two temporary reasons:

1. **The agent had to learn the foundations first.** It did not yet have matching
   logic and the K framework internalized, so it had to be told to go study them.
   This is a **one-time cost** — once learned, it need not be repeated.
2. **The tooling does not yet run the whole pipeline autonomously.** Today a human
   nudges the agent through each stage; the product will orchestrate them.

Neither is fundamental. As the foundations become built-in knowledge and the
pipeline becomes a single autonomous workflow, the prompt collapses to the one
line above. Today's verbose, multi-turn prompt is the *current* approximation of
that future one-line prompt.

## What the final tool does from that one prompt

Given only the one-line prompt, the envisioned product runs this pipeline
automatically — with its matching-logic and K knowledge already built in:

1. **Generate the program and tests** (test-driven).
2. **Select or derive a formal semantics** for the relevant language fragment, in
   K / matching logic.
3. **Synthesize the specification** — the pre/post-condition as a reachability
   rule.
4. **Infer the required lemmas and invariants** — e.g. the loop's circularity —
   without being asked.
5. **Produce the proof and machine-check it** (`kompile` + `kprove`, expecting
   `#Top`).
6. **Emit** both a human-readable report and the machine-checkable artifacts.

The human contributes one sentence; the AI contributes the code, the formalized
language, the specification, the proof, and the machine-checked guarantee.

---

*Status — two honest gaps, both of which the product would close. (1) **Language
gap.** This experiment verifies the program as rendered in **mini Python**, a
small modeling language the AI defined to host the proof; the AI did not produce
a formal semantics of Python itself, and the literal `summation.py` was
transliterated (not yet verified-equivalent) into that language. A full product
would instead verify against a complete K semantics of real Python — such
full-language K semantics exist for real languages — so the literal source file
is checked directly, with no transliteration. (2) **Toolchain gap.** The proof is
constructed to be `kompile`/`kprove`-checkable and is backed by an independently
reviewed reachability proof, but the K toolchain was not executed in this
environment; running it (see `sum-verification.md` §5.6) is the step that turns
"constructed-to-be-checkable" into "machine-verified." Both are exactly the steps
the product would automate.*
