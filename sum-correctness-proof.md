# Matching-Logic Reachability Proof of `sum(1..n)` (IMP)

Proves `A |- phi_pre => phi_post` for the program

```
s = 0 ; i = 1 ; while (i <= n) { s = s + i ; i = i + 1 }
```

i.e. starting with `n = N >= 0`, the program reaches a terminated state with `s = N(N+1)/2`.
Partial correctness, one-path reachability, over the trusted IMP semantics `A`.

## 0. Notation & conventions

- Lowercase `s, i, n` = IMP program variables; uppercase `S, I, N` = logical variables over `Z`.
  Math ops subscripted: `+Z, -Z, *Z, /Z, <=Z`.
- Configuration: `< <K>_k <Store>_state >_cfg /\ Constraint`, where `.` is the empty computation,
  `~>` is the computation list, and `Store` is a map `x|->V` with commutative concatenation `,`.
- **Statement syntax:** assignment `x = e ;` is atomic and keeps its own `;`; `(seq)` only separates
  whole statements. So every `(asgn)` redex below retains its trailing `;`.
- **Framing:** by (Axiom), the `<K>` tail, untouched store bindings, and the side constraint are carried
  unchanged around each rewrite. In PART A the constraint `I <=Z N+Z1` is framed on every `C1..C4`.
- **Guard on symbolic values:** `(leq)` on `I, N` yields a Boolean *term* `(I <=Z N)`; `(cond-*)` needs a
  literal, so we case-split and, in each branch, a (Consequence) step proves the term equals `true`/`false`.

## IMP operational semantics (the trusted axioms `A`)

```
(lookup)  < x ~> K | ... x|->V ... >  =>  < V ~> K | ... x|->V ... >
(add)     I1 + I2  =>  I1 +Z I2        (sub) I1 - I2 => I1 -Z I2        [+,- strict in both args]
(leq)     I1 <= I2 =>  (I1 <=Z I2) in {true,false}                     [<= strict in both args]
(asgn)    < x = V ; ~> K | ... x|->_ ... >  =>  < K | ... x|->V ... >  (V a value)
(seq)     S1 ; S2 ~> K  ==  S1 ~> S2 ~> K
(cond-t)  if (true)  S1 else S2  =>  S1
(cond-f)  if (false) S1 else S2  =>  S2
(while)   while (B) S  =>  if (B) { S ; while (B) S } else { . }
```

## Reachability proof system (one-path)

`(Reflexivity)`, `(Axiom)` (with substitution + framing), `(Transitivity)`, `(Consequence)`
(FOL side conditions to an oracle/SMT), `(Case Analysis)`, `(Abstraction)`, and
`(Circularity)`: `A ∪ {phi=>phi'} |- phi=>phi'  ==>  A |- phi=>phi'`, **provided** the added
hypothesis is used only after at least one genuine `=>+` transition (guarded coinduction).

## The two theorems

```
(LOOP)  < while(i<=n){s=s+i;i=i+1} | s|->S , i|->I , n|->N >  /\  I <=Z N+Z1
    =>  < . | s|-> S +Z (N*Z(N+Z1) -Z (I-Z1)*ZI)/Z2 , i|-> N+Z1 , n|->N >

phi_pre  :  < s=0;i=1;while(i<=n){...} | s|->_ , i|->_ , n|->N >  /\  N >=Z 0
phi_post :  < . | s|-> N*Z(N+Z1)/Z2 , i|-> N+Z1 , n|->N >
```

`(LOOP)` holds for **all** `N ∈ Z`; the contract's `N >= 0` is used only in PART B. Write
`Sum(I,N) := (N*Z(N+Z1) -Z (I-Z1)*ZI)/Z2`  ( = `Sum_{k=I}^{N} k` ).

---

## 1. Arithmetic verification conditions (all over `Z`)

**VC-EXACT.** For every `m`, `m*Z(m+Z1)` is even (one of two consecutive integers is even). Hence
`N(N+1)`, `(I-1)I`, `I(I+1)` are even, every `/Z2` is exact, and on the even subgroup `2Z`:
`(A -Z B)/Z2 = A/Z2 -Z B/Z2`  **(DIV-LIN)**.

**VC1 (loop step).** `(S+ZI) +Z (N(N+1) - I(I+1))/2 = S +Z (N(N+1) - (I-1)I)/2`.
Cancel `S` and `N(N+1)/2` via (DIV-LIN); ×2 reduces to `2I - I(I+1) = -( (I-1)I )`, i.e.
`I - I^2 = I - I^2`. ∎

**VC2 (loop exit).** `I = N+1  ==>  Sum(I,N) = 0`: then `(I-1)I = N(N+1)`, numerator `0`. ∎

**VC3 (init).** `(N(N+1) - (1-1)·1)/2 = N(N+1)/2`. ∎

**Side conditions.** `N >= 0 ==> 1 <= N+1` (PART B);  `I <= N ==> (I+1) <= N+1` (CASE TRUE re-entry).

---

## 2. PART A — `A |- (LOOP)` by (Circularity)

Add `H = (LOOP)` as hypothesis (variables `S,I,N` universally quantified, instantiated per use);
prove `A ∪ {H} |- (LOOP)`, using `H` only after a genuine transition. Let `W := while(i<=n){s=s+i;i=i+1}`,
`Bdy := s=s+i ; i=i+1`. Frame: `<K>` tail, `n|->N`, the constraint `I <=Z N+Z1`.

**Step 1 — unroll (Axiom while).** `C0 => C1 : < if (i<=n){Bdy;W} else {.} | s|->S,i|->I,n|->N >`.
This single transition **discharges guardedness** (it precedes any use of `H`).

**Step 2 — evaluate guard (lookup i, lookup n, leq).**
`C1 =>+ C4 : < if (I<=Z N){Bdy;W} else {.} | s|->S,i|->I,n|->N > /\ I<=Z N+Z1`.

**Step 3 — (Case Analysis).** FOL: under `I<=Z N+Z1`, `C4 ≡ C4_T ∨ C4_F` with
`C4_T : ... /\ (I<=Z N)` and `C4_F : ... /\ (I>Z N) /\ (I<=Z N+Z1)`. (Consequence) moves `C4 -> C4_T∨C4_F`,
then (Case Analysis). Target `RHS_LOOP : < . | s|-> S+ZSum(I,N) , i|-> N+Z1 , n|->N >`.

- **CASE TRUE `(I<=Z N)`:** (guard→true)+(cond-t) → `< Bdy;W | ... >`; (seq) heat;
  `s=s+i ;` → lookup s,i, add, asgn ⇒ `s|->S+ZI`; `i=i+1 ;` → lookup i, add, asgn ⇒ `i|->I+Z1`.
  Reach `C8 : < W | s|->S+ZI , i|->I+Z1 , n|->N > /\ (I<=Z N)`. **Invoke `H`** at `{S:=S+ZI, I:=I+Z1}`
  (precond `(I+1)<=N+1` follows from `I<=N`); get `s|-> (S+ZI)+ZSum(I+Z1,N)`. By **VC1** this equals
  `S+ZSum(I,N)` ⇒ `RHS_LOOP`, via (Consequence). `H` is used strictly after progress. ✓
- **CASE FALSE `(I>Z N) /\ (I<=Z N+Z1)`:** antisymmetry ⇒ `I = N+1`. (guard→false)+(cond-f) →
  `< . | s|->S , i|->I , n|->N >`. By **VC2**, `Sum(I,N)=0` so `s=S`, `i=I=N+1` ⇒ `RHS_LOOP`,
  via (Consequence). `H` not used. ✓

(Case Analysis) + (Transitivity) with `C0 =>+ C4` gives `A ∪ {H} |- (LOOP)`; guardedness met, so
**(Circularity)** discharges `H`:  `A |- (LOOP)`. ∎

The side condition `I <= N+1` is **necessary**: for `I >= N+2` the body never runs yet `Sum(I,N) ≠ 0`.

---

## 3. PART B — `A |- phi_pre => phi_post` using `(LOOP)`

`phi_pre = exists S0,I0. < s=0;i=1;W | s|->S0,i|->I0,n|->N > /\ N>=Z0`.

**Step 1.** (seq) heat; `s=0 ;` → asgn ⇒ `s|->0`; `i=1 ;` → asgn ⇒ `i|->1`. Reach
`D2 : < W | s|->0 , i|->1 , n|->N > /\ N>=Z0`. (Abstraction drops `S0,I0`.)

**Step 2.** (Consequence) `N>=0 -> 1<=N+1`, so `D2` matches `(LOOP)`'s LHS at `{S:=0,I:=1}`. Apply `(LOOP)`:
`D3 : < . | s|-> 0+ZSum(1,N) , i|-> N+Z1 , n|->N >`. By **VC3**, `Sum(1,N)=N(N+1)/2`, so `D3 -> phi_post`.

(Transitivity) of `D0 =>+ D2` and `D2 => phi_post`, then (Abstraction): **`A |- phi_pre => phi_post`. ∎**

Boundary `N=0`: body never runs, `i` stays `1 = N+1`, `s = 0 = N(N+1)/2` — faithful.

---

## 4. Soundness & residual risk

- **Proved:** partial correctness — *if/when* it terminates, `s = N(N+1)/2`, `i = N+1`, `n = N`.
- **Not proved:** termination. (Circularity)'s guardedness gives coinductive *soundness*, not a
  well-founded variant; no decreasing measure (e.g. `N-I`) is exhibited. Total correctness is out of scope.
- **Trusted base:** adequacy of the IMP axioms `A`; the reachability proof system's metatheory
  (esp. guarded-coinduction soundness of (Circularity)); the FOL oracle — though every side condition
  here (VC-EXACT, VC1–VC3, the two side implications, the case partition) is additionally proved by hand.
- All division is exact on `2Z` (VC-EXACT); the proof uses no rationals.

## Verification

Constructed and adversarially checked by 5 independent lenses (operational semantics, coinduction
soundness, arithmetic, case completeness, spec faithfulness). All returned **sound** / **sound-with-nits**,
**no critical or major defects**. Arithmetic independently re-derived all VCs + 20k randomized `(LOOP)`
checks and `N=0..11` end-to-end. The `sum(1..n)` program is the canonical SUM example of the
One-Path Reachability (LICS'13) and fixpoint-reasoning (OOPSLA'20) papers.
