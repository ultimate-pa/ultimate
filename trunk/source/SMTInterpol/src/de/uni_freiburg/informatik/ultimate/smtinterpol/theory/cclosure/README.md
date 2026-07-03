# Congruence Closure Theory (`smtinterpol.theory.cclosure`)

This package implements the **theory of equality** (congruence closure) for SMTInterpol. It maintains an equality graph over terms, propagates equalities and disequalities implied by transitivity and congruence, detects conflicts, and cooperates with other theories (linear arithmetic, arrays, datatypes) via Nelson-Oppen style combination.

---

## Package Overview

| Class | Role |
|------|------|
| **CClosure** | Main theory engine: implements `ITheory`, owns the equality graph, handles literal setting, propagation, conflict detection, and backtracking. |
| **CCTerm** | Abstract node in the equality graph; holds union-find fields, parent info, and merge/undo state. |
| **CCBaseTerm** | Leaf node: represents a function symbol or anonymous term (constant / non-application). |
| **CCAppTerm** | Application node: represents `f(args...)`; stores function and argument CCTerms and parent links. |
| **CCEquality** | DPLL atom for an equality literal between two CCTerms; may be linked to an LAEquality for shared terms. |
| **CCParentInfo** | Per equivalence class: lists of CCAppTerms that have a member as func/arg at a given (function, argument position), plus reverse triggers. |
| **CCTermPairHash** | Hash structure mapping pairs of congruence class representatives to `Info`: equalities, disequality, compare triggers. |
| **CongruencePath** | Builds equality paths between CCTerms along `mEqualEdge` and congruences; used for conflict clauses and proof annotations. |
| **WeakCongruencePath** | Extends CongruencePath for array theory: weak equivalence paths, store edges, and weak/strong path distinction. |
| **CCAnnotation** | Proof annotation for CC/array/DT lemmas: rule kind, diseq pair, paths, weak indices. |
| **CCProofGenerator** | Converts CCAnnotation (and array/DT annotations) into proof terms (resolution with auxiliary CC lemmas). |
| **CompareTrigger** | E-matching: activated when two CCTerms become equal (compare on pair). |
| **ReverseTrigger** | E-matching: activated when a new application with a given function (and optionally argument at a position) appears. |
| **DTReverseTrigger** | ReverseTrigger for datatypes: applies DT rules when constructor/selector applications appear. |
| **DataTypeLemma** | Describes a datatype lemma (rule kind, main equality, reason pairs, annotation for proofs). |
| **ArrayTheory** | Array solver built on CClosure; uses weak equivalence and ArrayNode graph. |
| **DataTypeTheory** | Datatype solver built on CClosure; propagates equalities from constructors/selectors/testers. |
| **ModelBuilder** | Assigns values to CCTerm equivalence class representatives for model construction (with Array/DT support). |

---

## Core Data Structures

### Equality graph (union–find style)

- **Nodes** are `CCTerm` (either `CCBaseTerm` or `CCAppTerm`). Each term has:
  - **`mRep`**: next representative along the chain; `mRep == this` for the class representative.
  - **`mRepStar`**: canonical representative of the congruence class (all nodes in the class point to the same `mRepStar`).
  - **`mEqualEdge`** / **`mOldRep`** / **`mReasonLiteral`**: one outgoing “equality edge” per node (except the root of the class). Edges form a spanning tree of the class; they record the merge (and optional CCEquality reason) for undo.
- **Congruence classes** are maintained by merging two classes when an equality is set or when two applications are congruent (same function representative, same argument representatives). The smaller class is merged into the larger; edges are inverted so the merged node has a single outgoing edge to the other class.

### Parent info and congruence

- **`CCParentInfo`** (reachable from the class representative) is a list of entries, one per (function symbol, argument position). Each entry stores:
  - **`mCCParents`**: the `CCAppTerm.Parent` nodes (i.e. applications) that have a term in this class as function or argument at that position.
  - **`mReverseTriggers`**: E-matching reverse triggers for that (function, position).
- When two classes are merged, their parent infos are merged. For each matching (function, position), pairs of applications with same func-rep and same arg-rep are detected as **congruent** and enqueued as pending congruences; they are actually merged at **checkpoint** (see below).

### Pair hash and literals

- **`CCTermPairHash`** maps unordered pairs of **representatives** to **`Info`**:
  - **`mEqlits`**: CCEquality entries for that pair (equality literals).
  - **`mDiseq`**: one disequality literal that has been set for that pair (if any).
  - **`mCompareTriggers`**: compare triggers for that pair.
- When two classes are merged, the pair hash is updated: equalities and triggers for the merged pair are processed (propagation or conflict); for other pairs, the info of the merged class is joined into the new representative’s side.

---

## Main Algorithms

### Setting a literal (`setLiteral`)

- **Equality** `t1 = t2`: if `t1.mRepStar != t2.mRepStar`, call `merge(t1, t2, eq)`. If the pair already has a disequality, merge produces a conflict and the cycle is explained by `computeCycle(eq)`.
- **Disequality** `t1 != t2`: record the diseq in the pair hash for `(t1.mRepStar, t2.mRepStar)` and propagate negated equalities for all equalities in that pair’s list.

### Merge (`CCTerm.merge` / `mergeInternal`)

1. **Conflict check**: if the two classes have a recorded disequality, build a conflict clause (anti-cycle) and return it.
2. **Shared terms**: if both classes have a shared term (for linear arithmetic), create the corresponding CCEquality (and LAEquality) so that the other theory sees the equality.
3. **Invert** equality edges on the source side so the merged node has one outgoing edge.
4. **Link** the source class to the destination with one new equality edge; record merge on the undo stack.
5. **Update** `mRep` / `mRepStar` and member lists for the merged class.
6. **Join** pair-infos: for the pair (dest, source), propagate equalities and activate compare triggers; for other pairs, merge into the destination’s pair hash.
7. **Congruence**: for matching parent positions, find pairs of applications with same func-rep and arg-rep; add them to **pending congruences** (merged at checkpoint).

### Checkpoint and pending congruences

- **`checkpoint`** (and `finalCheck`) calls **`buildCongruence`**: drain the queue of pending congruences and merge each pair. Any conflict from merge is returned.
- Congruences are not applied immediately so that the order of operations and undo remain consistent.

### Backtracking

- **`mUndoStack`** stores merge and separation steps. On **decreasedDecideLevel**, the stack is popped back to the size recorded for that level; each popped frame either **undoes a merge** (restore rep, unjoin members and pair infos, unmerge parent infos) or **undoes a disequality** (clear `mDiseq` for that pair).
- **`mRecheckOnBacktrackLits`** and **`mRecheckOnBacktrackCongs`**: after backtrack, the engine rechecks whether previously propagated literals or congruences are still implied and re-enqueues them if so.

---

## Conflict Clauses and Proofs

### Cycle (disequality conflict)

- When an equality is set to false but the two terms are already in the same class, **`computeCycle(eq)`** is used: **CongruencePath** walks from `eq.getLhs()` to `eq.getRhs()` along equality edges and congruences, collecting the CCEquality literals that justify the path. The conflict clause is the negated equality plus the negations of those literals.

### Anti-cycle (equality conflict)

- When adding an equality would unite two classes that have a disequality, **`computeAntiCycle(eq)`** temporarily adds the edge from the eq’s lhs to rhs, then runs the same path computation on the disequality to get a conflict clause.

### Proof annotations

- **CongruencePath** (and **WeakCongruencePath** for arrays) record **SubPath**s (and **WeakSubPath**s with indices). These are stored in **CCAnnotation** together with the rule kind (e.g. `CONG`, `TRANS`, `READ_OVER_WEAKEQ`, `WEAKEQ_EXT`, or datatype rules).
- **CCProofGenerator** turns a **CCAnnotation** into a proof term: it builds auxiliary CC lemmas for each subpath that is a congruence or strong path, then builds a resolution proof that combines the main lemma with these auxiliary lemmas.

---

## Theory Combination

- **Shared terms** (with linear arithmetic): when a CCTerm is marked shared, the engine propagates equalities between shared terms in the same class and creates/links **LAEquality** atoms so the LA solver sees the equality.
- **ArrayTheory** and **DataTypeTheory** use the same CClosure graph. They register triggers and call back into CClosure to create CCTerms and CCEqualities; conflict clauses and proofs are produced via **CongruencePath** / **WeakCongruencePath** and **CCAnnotation** / **CCProofGenerator**.

---

## Signature Trigger   (Congruence & E-Matching)

- **SignatureTrigger**: A trigger watches a signature, which is an identifier plus an array of ccterm representatives.  When merging classes the signature is updated.  If two triggers have the same signature, they are merged and some action is executed.
- **CongruenceTrigger**: A signature trigger for every function application.  The merge operation propagates the congruence.
- **FindTriggerTrigger**: A trigger watching on function symbol and containing FindTrigger and/or applications on this function symbol.  A merge triggers every find trigger with every application.  Since the signature is only the function symbol, all find trigger and all applications of the function symbol are merged.
- **ReverseTriggerTrigger**: Similarly a trigger watching on a function symbol and one of its args containing ReverseTrigger and/or function applications.  A merge triggers every reverse trigger with every application that matches that argument.

## E-Matching Trigger.

- **CompareTrigger**: registered for a pair of CCTerms; **activated** when that pair’s representatives become equal (during merge). Used for instance for quantifier instantiation.
- **ReverseTrigger**: registered for a (function symbol, argument position). **Activated** when a new CCAppTerm appears that has a term in the relevant position (e.g. from **createAppTerm** or when an argument is merged into that position). **DTReverseTrigger** implements datatype-specific behaviour (e.g. selector/constructor/tester rules).
- **MasterReverseTrigger**: a find trigger that is registered for a function symbol for every position where a reverse trigger is created.  This will watch the i-th argument to enable the reverse trigger mechanism for this argument.

---

## Model Building

- **ModelBuilder** is invoked with the current CClosure, terms, model, theory, and evaluator. It groups representative CCTerms by sort, then fills the model in a sort-dependency order: datatypes via **DataTypeTheory**, arrays via **ArrayTheory**, and other sorts by assigning representative terms and filling function interpretations.

---

## File Summary

- **CClosure.java** – Main engine; term creation; merge/separate; checkpoint; backtrack; pair hash and triggers.
- **CCTerm.java** – Union-find, equality edges, parent info, merge/undoMerge, shared-term handling.
- **CCBaseTerm.java** – Base terms (symbols / anonymous terms).
- **CCAppTerm.java** – Application terms; parent lists; integration with triggers.
- **CCEquality.java** – Equality atom; link to LAEquality for shared terms.
- **CCParentInfo.java** – Parent lists and reverse triggers per (function, position).
- **CCTermPairHash.java** – Pair → Info (equalities, diseq, compare triggers).
- **CongruencePath.java** – Path computation for cycles and proof annotations.
- **WeakCongruencePath.java** – Weak paths and array lemmas (read-over-weakeq, weakeq-ext, etc.).
- **CCAnnotation.java** – Rule kinds and path storage for proofs.
- **CCProofGenerator.java** – Annotation → proof term (with auxiliary lemmas).
- **CompareTrigger.java** / **ReverseTrigger.java** – E-matching trigger interfaces.
- **DTReverseTrigger.java** – Datatype reverse trigger implementation.
- **DataTypeLemma.java** – Datatype lemma description for proofs and propagation.
- **ArrayTheory.java** – Array solver (weak equivalence, ArrayNode).
- **DataTypeTheory.java** – Datatype solver (constructors, selectors, testers).
- **ModelBuilder.java** – Model construction from equivalence classes and sorts.
