# Congruence Closure Theory (`smtinterpol.theory.cclosure`)

This package implements the **theory of equality** (congruence closure) for SMTInterpol. It maintains an equality graph over terms, propagates equalities and disequalities implied by transitivity and congruence, detects conflicts, and cooperates with other theories (linear arithmetic, arrays, datatypes) via Nelson-Oppen style combination.

Two design decisions shape the current code and are worth knowing up front:

- **Affine (offset) classes.** A congruence class is not a set of equal terms but an *affine* class: every member `t` carries a rational offset to the representative, `value(t) == value(rep) + t.mOffsetToRep`. Plain equality is the special case offset `0`. This lets linear arithmetic post `a = b + k` directly instead of only `a = b`, and makes `x+5` in `f(x+5)` a first-class congruence argument. The feature is switched by the option `:offset-equalities` (default true, queried through `CClosure.createOffsetEqualities()`); with it off every offset is `ZERO` and the whole machinery degenerates to plain congruence closure. See `SMTInterpol/doc/offset-equality-plan.md` for the full design and its invariants.
- **Signature triggers instead of parent lists.** Congruence detection and e-matching triggers no longer use per-class parent lists (`CCParentInfo` is gone). Instead there is one global map from *signature* (an identifier plus an array of argument values) to trigger; classes hold back-references into that map and signatures are rehashed and merged at checkpoint.

---

## Package Overview

| Class | Role |
|------|------|
| **CClosure** | Main theory engine: implements `ITheory`, owns the equality graph, the pair hash and the signature map, handles literal setting, propagation, conflict detection, and backtracking. |
| **CCTerm** | Node in the equality graph; union-find fields (`mRepStar`, `mRep`, `mOffsetToRep`), equality edges, pair infos, signature back-refs, shared term, merge/undo. Implements `CCParameter` with offset zero. |
| **CCBaseTerm** | Leaf node: represents a function symbol or anonymous term (constant / non-application). |
| **CCAppTerm** | Application node: represents `f(args...)`; arguments are `CCParameter`s, so an argument may carry a constant offset. Holds its congruence trigger, find trigger and the reverse-trigger signatures created for it. |
| **CCParameter** | A *value* of the form `ccterm + constant`: the interface every consumer of an argument, array index or shared-term comparison deals with. Defines value identity (`sameValueAs`, `getValueKey`) and the term rendering `getFlatTerm`/`addConstant`. |
| **OffsettedCCTerm** | The only implementation of `CCParameter` with a non-zero offset; `CCParameter.of` returns a bare `CCTerm` for offset zero, so the offset-free case allocates nothing. |
| **CCEquality** | DPLL atom for an equality `getLhs() == getRhs() + getOffset()` between two CCTerms; may be linked to an `LAEquality` for shared terms. Records the separating disequality (`mDiseqReason`) and its orientation. |
| **CCTermPairHash** | Hash structure mapping a *relationship* `value(A) == value(B) + offset` between two representatives to an `Info`: equality literals, the separating disequality, compare triggers. Several offsets between the same endpoints coexist. |
| **SignatureTrigger** | Key of the global signature map: an opaque id plus a `CCParameter[]`, hashed and compared on each argument's representative **and** offset to it. Subclasses define what happens when two triggers get the same signature. |
| **SignatureBackRef** | Back-reference from a class member to one argument position of one signature; the merge pushes these onto the signature todo so the signature is rehashed at checkpoint. |
| **CongruenceTrigger** | Signature trigger for a function application. Merging two of them means the two applications are congruent, which is enqueued as a pending congruence. |
| **FindTriggerTrigger** | Signature trigger keyed on the function symbol alone, holding find triggers and applications of that symbol. A merge cross-activates every trigger with every application. |
| **ReverseTriggerTrigger** | Signature trigger keyed on a `MasterReverseTrigger` (function symbol + argument position) and the watched argument *value*, holding reverse triggers and matching applications; a merge cross-activates them. |
| **MasterReverseTrigger** | The find trigger installed per (function symbol, argument position), unified per engine. When an application of the symbol appears it registers a `ReverseTriggerTrigger` for that application's argument value. |
| **CompareTrigger** | E-matching: activated when two values become equal (same class at the matching offset). |
| **ReverseTrigger** | E-matching: activated when an application with a given function symbol (and optionally a given argument value at a position) appears. |
| **DTReverseTrigger** | ReverseTrigger for datatypes: applies DT rules when constructor/selector/tester applications appear. |
| **DataTypeLemma** | Describes a datatype lemma (rule kind, main equality, reason pairs, annotation for proofs). |
| **CongruencePath** | Builds equality paths between CCTerms along `mEqualEdge` and congruences; used for conflict clauses, unit clauses and proof annotations. Owns the single offset-aware conflict explainer `computeMergeConflictCycle`. |
| **WeakCongruencePath** | Extends CongruencePath for array theory: weak equivalence paths, store edges, select/const edges, weak/strong path distinction. |
| **CCAnnotation** | Proof annotation for CC/array/DT lemmas: rule kind, diseq pair, paths as `CCParameter[][]`, weak indices, select edges. |
| **CCProofGenerator** | Converts CCAnnotation (and array/DT annotations) into proof terms (resolution with auxiliary CC lemmas), keying facts on `OffsetPair`. |
| **ArrayTheory** | Array solver built on CClosure; uses weak equivalence and ArrayNode graph, with all indices and element values keyed by value (`getValueKey`). |
| **DataTypeTheory** | Datatype solver built on CClosure; propagates equalities from constructors/selectors/testers. |
| **ModelBuilder** | Assigns values to CCTerm equivalence class representatives for model construction (with Array/DT support), keeping the whole offset range of a class clear of other values. |

---

## Core Data Structures

### Equality graph (weighted union–find)

- **Nodes** are `CCTerm` (either `CCBaseTerm` or `CCAppTerm`). Each term has:
  - **`mRep`**: next representative along the chain; `mRep == this` for the class representative.
  - **`mRepStar`**: canonical representative of the congruence class (all nodes in the class point to the same `mRepStar`; there is no path compression, so this pointer is always exact).
  - **`mOffsetToRep`**: the offset to that representative, `value(this) == value(mRepStar) + mOffsetToRep`. A representative has offset `ZERO` (asserted in `invariant()`).
  - **`mEqualEdge`** / **`mOldRep`** / **`mReasonLiteral`**: one outgoing “equality edge” per node (except the root of the class). Edges form a spanning tree of the class; they record the merge (and the optional `CCEquality` reason, `null` for a congruence) for undo and for path computation.
- **Congruence classes** are merged when an equality is set or when two applications turn out congruent. The smaller class is merged into the larger; edges are inverted so the merged node has a single outgoing edge to the other class.

### Values: `CCParameter`

An argument of the shape `ccterm + constant` is *not* reified as its own CCTerm (that would need a definitional tautology `(+ x 5) = x + 5` in every proof). Instead the constant is intrinsic to the use site: `CCAppTerm.mArgs` is a `CCParameter[]` and `getArgParam(i)` is the only argument accessor, so a caller that wants the offset-free node has to say `getArgParam(i).getCCTerm()`.

Two identities must not be confused:

- **value identity** `(getRepresentative(), getOffsetToRep())` — `sameValueAs`, `getValueKey()`. It *changes on merge*, so it may only key maps that are rebuilt after merges (the array theory does exactly that).
- **structural identity** `(getCCTerm(), getOffset())` — `OffsettedCCTerm.equals`. Stable; this is what proof and interpolation keys use.

### Pair hash and literals

- **`CCTermPairHash`** maps a relationship `value(A) == value(B) + offset` between two **representatives** to an **`Info`**:
  - **`mEqlits`**: `CCEquality` entries for that relationship.
  - **`mDiseq`**: the disequality literal that has been set for it (if any).
  - **`mCompareTriggers`**: compare triggers waiting for it.
  - **`mOffset`** is final and part of the key, so `a == b` and `a == b + 5` are two distinct infos with the same endpoints. `offsetHash` orients the offset by the endpoints' hash codes, so that `(A,B,off)` and `(B,A,−off)` (the same fact) hash alike while `(A,B,off)` and `(A,B,−off)` do not — cuckoo hashing degrades badly on structured collisions.
- Equality atoms and compare triggers are inserted into the info of every intermediate representative pair (`insertEqualityEntry`, `insertCompareTrigger`), with the offset translated as the walk moves up to the representative, so unmerging restores the pre-merge state.

### Signatures: the congruence and trigger index

- A **`SignatureTrigger`** is an id plus a `CCParameter[]`. Hash and equality use each argument's representative *and* its `getOffsetToRep()`, with disjoint salts for the two contributions, so two applications match only if their arguments have the same value — same class **and** same offset.
- **`CClosure.mSignatureTriggers`** is the global map from signature to trigger; **`mSignatureTodo`** is the list of signatures waiting to be (re-)inserted.
- **`SignatureBackRef`** links a class to the signatures one of its members occurs in. The representative holds all back-refs of the class, non-representatives the sublists of their own subtree, so a merge/unmerge can join/unjoin them like the member lists.
- The trigger subclasses define what a signature collision means: a congruence (`CongruenceTrigger`), a find-trigger activation (`FindTriggerTrigger`), or a reverse-trigger activation (`ReverseTriggerTrigger`).

---

## Main Algorithms

### Setting a literal (`setLiteral`)

- **Equality** `t1 == t2 + k`:
  - different classes: `merge(t1, t2, eq)`.
  - same class: consistent only if the offset the two terms already have matches `k`; a mismatch (e.g. asserting `x == x + 1`) is a conflict, explained by `computeAntiCycle(null, false, eq)`.
- **Disequality**: if the two sides are in the same class, it is a conflict only if they sit at exactly the offset the equality claims (`computeCycle`); if the offsets differ the disequality already holds and there is nothing to do. Otherwise `separate` records the diseq in the pair info for the representative pair *at that offset* and propagates negated equalities for the equalities registered there.
- A linked `LAEquality` is propagated (or the clash with an already decided one reported) in either case.

### Merge (`CCTerm.merge` / `mergeInternal`)

1. **Offset check**: if both terms are already in the same class, the merge is a no-op when the existing offset difference equals the one implied by the reason (`reasonDiff`), and a conflict otherwise (`computeCongruenceAntiCycle` for a congruence).
2. **Compute `delta`**: the offset the source representative gets relative to the destination, `delta = reasonDiff − lhs.mOffsetToRep + this.mOffsetToRep`.
3. **Conflict check before mutating anything**: a disequality registered for the two classes *at exactly `delta`* (`computeMergeDiseqCycle`), or a shared-term clash where the implied equality cannot even be built (`computeSharedConflictCycle`), returns immediately — the union-find is still pristine, so no add-then-undo dance is needed and the conflict explainer never sees a half-merged state.
4. **Shared terms**: if both classes have a shared term (for linear arithmetic), create the corresponding `CCEquality` (and `LAEquality`) at the resulting offset, so the other theory sees the equality.
5. **Invert** equality edges on the source side, **link** the source class to the destination with one new equality edge, record the merge on the undo stack.
6. **Rehash signatures** of the source class *before* the offsets change (so `SignatureTrigger.recomputeHashCode` still sees the old effective offset and shifts it by `delta`), then update `mRep`/`mRepStar` and add `delta` to every member's `mOffsetToRep`, and join the member lists.
7. **Join pair infos**: infos between the two merged classes are resolved directly — equalities at exactly `delta` are propagated *true* and compare triggers fire; all others are propagated *false*, with `mDiseqReason == null`, since no separating literal is involved and the path itself is the explanation. Infos to other classes are re-keyed from `(src, other, k)` to `(dest, other, k − delta)`.
8. **Join the signature back-refs** into the destination.

### Checkpoint: signature todo and pending congruences

- **`checkpoint`** (and `finalCheck`) call **`buildCongruence`**, which alternates two work lists until both are empty:
  - drain **`mSignatureTodo`**: insert each signature into `mSignatureTriggers`; if an equal signature is already there, merge the two triggers (which enqueues a pending congruence, or cross-activates find/reverse triggers) and push a `TriggerMergeUndoEntry`.
  - drain **`mPendingCongruences`**: merge each congruent pair of applications, returning any conflict.
- Congruences are not applied immediately, so that the order of operations and the undo stack stay consistent.

### Backtracking

- **`mUndoStack`** holds three kinds of entries: `MergeUndoInfo` (undo a merge: invert edges, restore `mRep`/`mRepStar`, subtract `delta` from the members' offsets, unjoin members, pair infos and back-refs, rehash the signatures back), `SepUndoInfo` (clear `mDiseq` of that pair info), and `TriggerMergeUndoEntry` (unmerge two signature triggers and put the previous one back on the signature todo). `decreasedDecideLevel` pops back to the size recorded for that level.
- **`mRecheckOnBacktrackLits`**: literals that were propagated at creation time may sit at the wrong decision level; `backtrackComplete` rechecks whether they are still implied — an equality only if the two sides are in one class *at its offset*, a disequality only if a separating diseq is registered at the matching offset — and re-propagates them if so.

---

## Conflict Clauses and Proofs

### Cycle

- When an equality is set false while its two sides are already connected at exactly its offset, **`computeCycle(eq)`** walks from `eq.getLhs()` to `eq.getRhs()` along equality edges and congruences and collects the justifying literals. The same clause serves as the unit clause when the equality was propagated true.

### The single merge-conflict explainer

Every other conflict goes through **`CongruencePath.computeMergeConflictCycle(lhs, rhs, offset, equality, lhsDiseq, rhsDiseq, diseq, produceProofs)`**: a bridge edge `lhs == rhs + offset` plus the class paths that contradict a known disequality. Three knobs span all cases:

| knob | meaning |
|---|---|
| `lhsDiseq == rhsDiseq` | same-class (anti-cycle); otherwise cross-class |
| `equality == null` | congruence bridge (justified by the argument equalities); otherwise an equality literal |
| `diseq == null` | trivial/arithmetic disequality (EQ/LA discharged, no positive literal); otherwise a literal carried positively |

The wrappers in `CClosure` are `computeAntiCycle` (an equality against a separating diseq, or against a deviating offset in its own class), `computeCongruenceAntiCycle` (congruent applications already in one class at a non-zero offset), `computeMergeDiseqCycle` and `computeSharedConflictCycle`.

Each half of such a path is built **inside one class**: `mOffsetToRep` is relative to a node's own representative, so a path spanning two classes (e.g. over a freshly added, not-yet-united merge bridge) would mix reference frames and produce garbage offsets. The two halves are rendered separately and stitched across the bridge.

### Proof annotations

- **CongruencePath** (and **WeakCongruencePath** for arrays) record **SubPath**s (and **WeakSubPath**s with an index and, where needed, the select/const edge that justifies the weak step). `SubPath` stores offset-free CCTerms; **`getParams(anchor)`** renders them as `CCParameter`s so that every node denotes the same value as the anchor, which must be one of the path's two endpoints and fixes only the absolute base.
- **`mVisited`** keys subpaths by the *offset-free* end terms, so two requests differing only by a constant share one subpath; the consumers absorb the per-use difference. **`drainTodo`** collects a path only after its congruence dependencies (re-enqueue discipline), as `CCAnnotation` requires; paths that are inlined by hand are built via `computePath` without entering `mVisited` or `mAllPaths`.
- **CCAnnotation** stores the rule kind (`CONG`, `TRANS`, `READ_OVER_WEAKEQ`, `WEAKEQ_EXT`, the datatype rules, …), the diseq pair and the paths as `CCParameter[][]`.
- **CCProofGenerator** turns a CCAnnotation into a proof term: it builds auxiliary CC lemmas for congruences and strong subpaths and resolves them against the main lemma. Its maps are keyed on **`OffsetPair`**, the *structural* offset between two CCTerms, so different renderings of the same fact collapse to one key while genuinely different offsets stay apart.

---

## Theory Combination

- **Shared terms** (with linear arithmetic): when a CCTerm is marked shared, the engine propagates equalities between shared terms of one class and creates/links **LAEquality** atoms so the LA solver sees them. With offsets on, the shared entity is the **offset-free** value, and the equality carries the constant difference of the two members' offsets.
- **Model-based theory combination** uses `CClosure.getNumericClashSlots()`: instead of comparing whole numeric terms it enumerates, on demand in `finalCheck`, the argument `CCParameter`s that occupy one (function symbol, argument position) — plus the values watched by installed reverse triggers, plus one group per array sort for select/`const` element values, which `ArrayTheory` reads as distinct values. Two members of a slot with equal model value in distinct affine classes are an equality MBTC can propose.
- **ArrayTheory** and **DataTypeTheory** use the same CClosure graph. They register triggers and call back into CClosure to create CCTerms and CCEqualities; conflicts and proofs are produced via **CongruencePath** / **WeakCongruencePath** and **CCAnnotation** / **CCProofGenerator**. All array indices and element values are handled as `CCParameter`s and keyed by `getValueKey()`, which is sound because the weak-equivalence structures are rebuilt whenever a representative or offset can have moved.

---

## Triggers

### Signature triggers (congruence and e-matching plumbing)

- **SignatureTrigger**: watches a signature — an id plus argument values. Signatures are rehashed when a class merges and re-inserted at checkpoint; two triggers with the same signature are merged, and the subclass decides what that means.
- **CongruenceTrigger**: one per function application. A merge means the two applications are congruent, so the congruence is enqueued (`addPendingCongruence`).
- **FindTriggerTrigger**: keyed on the function symbol alone, holding find triggers and applications of that symbol. A merge activates every find trigger with every application. `getAllFuncApps` reads the applications out of it.
- **ReverseTriggerTrigger**: keyed on a `MasterReverseTrigger` (function symbol + argument position) and the watched argument value, holding reverse triggers and matching applications; a merge activates every trigger with every matching application. Because the signature is keyed on the argument *value*, the reverse-trigger machinery is offset-aware for free.

### E-matching triggers

- **CompareTrigger**: registered for a pair of values; **activated** when they become equal, i.e. their classes merge at exactly the trigger's offset. Used e.g. for quantifier instantiation.
- **ReverseTrigger**: registered for a function symbol, optionally with an argument value at a position. **Activated** when a matching application appears (a new `createAppTerm`, or an argument moving onto the watched value). **DTReverseTrigger** implements the datatype-specific behaviour (selector/constructor/tester rules).
- **MasterReverseTrigger**: the find trigger installed per (function symbol, argument position), unified per engine. Its activation is what creates the per-application `ReverseTriggerTrigger`s (remembered on the application so they are removed with it on `pop`).

---

## Model Building

- **ModelBuilder** is invoked with the current CClosure, terms, model, theory, and evaluator. It groups representative CCTerms by sort, then fills the model in a sort-dependency order: datatypes via **DataTypeTheory**, arrays via **ArrayTheory**, and other sorts by assigning representative terms and filling function interpretations.
- With offsets, a class is used at a whole *range* of values (`value(rep) + offsetToRep` over its members and argument positions). ModelBuilder therefore records the minimal and maximal use-site offset per numeric class, shifts a freshly chosen value by the minimum and registers the maximum, so the entire range stays clear of other classes' values. **`getModelValue(CCParameter)`** is the only value accessor — a bare-CCTerm accessor would silently drop a member's offset.

---

## File Summary

- **CClosure.java** – Main engine; term creation; merge/separate; checkpoint; backtrack; pair hash, signature map and triggers; clash slots for MBTC.
- **CCTerm.java** – Weighted union-find, equality edges, offsets to the representative, pair infos, signature back-refs, merge/undoMerge, shared-term handling.
- **CCBaseTerm.java** – Base terms (symbols / anonymous terms).
- **CCAppTerm.java** – Application terms; `CCParameter` arguments; the triggers belonging to the application.
- **CCParameter.java** – The `ccterm + constant` value interface: value identity, term rendering, `of`/`addConstant`.
- **OffsettedCCTerm.java** – The non-zero-offset `CCParameter` implementation.
- **CCEquality.java** – Offset equality atom; diseq reason and orientation; link to LAEquality for shared terms.
- **CCTermPairHash.java** – (Pair, offset) → Info (equalities, diseq, compare triggers).
- **SignatureTrigger.java** – Signature key (id + argument values), rehashing, merge/undoMerge, back-ref management.
- **SignatureBackRef.java** – Back-reference from a class to one argument position of one signature.
- **CongruenceTrigger.java** / **FindTriggerTrigger.java** / **ReverseTriggerTrigger.java** / **MasterReverseTrigger.java** – The signature trigger kinds: congruence, find trigger, reverse trigger, and the per-(symbol, position) master find trigger.
- **CompareTrigger.java** / **ReverseTrigger.java** – E-matching trigger interfaces.
- **DTReverseTrigger.java** – Datatype reverse trigger implementation.
- **DataTypeLemma.java** – Datatype lemma description for proofs and propagation.
- **CongruencePath.java** – Path computation for cycles, the merge-conflict explainer, and proof annotations.
- **WeakCongruencePath.java** – Weak paths and array lemmas (read-over-weakeq, weakeq-ext, etc.).
- **CCAnnotation.java** – Rule kinds, diseq pair, paths, weak indices and select edges for proofs.
- **CCProofGenerator.java** – Annotation → proof term (with auxiliary lemmas), keyed on `OffsetPair`.
- **ArrayTheory.java** – Array solver (weak equivalence, ArrayNode).
- **DataTypeTheory.java** – Datatype solver (constructors, selectors, testers).
- **ModelBuilder.java** – Model construction from equivalence classes and sorts, respecting each class's offset range.
