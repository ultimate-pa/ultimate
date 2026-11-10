# Better correctness witnesses from k-induction

Branch: `valueanalysis` (worktree `ultimate-valueanalysis`). Commit **and push** (`origin valueanalysis`) after each of the three changes below. First step of implementation: copy this plan to `plans/kinduction-correctness-witnesses.md` in the repo (memory rule).

## Context

A SAFE verdict from k-induction almost always comes with a trivial correctness witness (`content: []`). Measured on the SV-COMP 2027 ReachSafety run of UParalizer (version 5581494f, which already contains every k-induction witness commit up to 3601b896a7):

- **Sample 1:** 1200 random TRUE logs.
  - k-induction proved 1127 of them.
  - Only **2** of those 1127 got a non-trivial invariant into the witness.
  - 2089 of the 2235 `correct-unconfirmed` TRUE results in the whole run are in `hardness`.
- **Sample 2:** 366 proofs by k-induction.
  - 255 had "Main: using the invariants of the k-induction proof". **All 255 were k=1**, 254 of them with no injected invariant. The invariant is then `true` at every loop head, and `FloydHoareUtils.createInvariantResults` drops `"1"`/`"true"`, which leaves an empty witness.
  - 111 had "k-induction proof without invariants". Of these, 58 were k=1 and 53 were k≥2. **No proof with k≥2 got any invariants.**
  - The causes were always timeouts. 59 were `ToolchainCanceledException`, i.e. the 1.5 s timer of `KInductionWorkerThread.computeWitnessInvariantsWithin`. 45 were `SMTLIBException … Connection to SMT solver broken / EOF`: the k-induction solver is bitwuzla, and the watchdog's SIGINT kills it (exit code 130) about 1.6 s after `is safe true`. That is the same timeout. "Could not eliminate quantifiers" never occurred.
- **The work these computations do:**
  - k=1 with no injected invariant: `isInductive` re-proves the step case, once per step pair, as a top-level `(exists …)` assertion, only to produce all-`true` invariants. The witness is then empty either way.
  - k≥2: `PartialQuantifierElimination` over k composed steps, plus the same quantified consecution check. Neither fits in 1.5 s.
- **The hardness programs** have the shape `while(1){ updateLast(); havoc inputs; step(); __VERIFIER_assert(property()); }`. Their loop body establishes the property from any state, so `true` is a genuine 1-inductive invariant. That is why k=1 needs nothing. A non-trivial witness there needs invariants the proof did not use.

**Not a loss.** `Boogie2ACSL` returns null for a disjunction with an untranslatable disjunct under over-approximation. That is equivalent to `true`, so it is correct.

**Pipeline, for reference:**
- `KInduction.computeWitnessInvariants` (`Library-KInduction/.../KInduction.java:682`) computes `J_h` for k=1, else QE of `J_h ∧ noErrorWithinK(h)`, then checks the result with `isInductive` (747).
- `KInductionWorkerThread.computeWitnessInvariants[Within]` (`TraceAbstraction/.../parallel/kinduction/KInductionWorkerThread.java:280-368`) runs it under a 1.5 s + 0.5 s budget. It fails on a head at several call sites and on out-of-scope variables.
- `ParallelNwaCegarLoop.kInductionAnnotation` (643-668) gives up if the head set ≠ `mIcfg.getLoopLocations()`. On failure it calls `setProof(emptyMap)`.
- `TraceAbstractionStarter` → `FloydHoareUtils.createInvariantResults` → `WitnessInvariant` annotation → `YamlCorrectnessWitnessGenerator`.

**Key soundness fact used below.** Once the whole annotation (INIT `true`, every head and waypoint) is proven inductive on the pc transition system, each invariant in it holds in every reachable state. A witness may therefore carry **any subset** of the annotation. The all-or-nothing rule is only needed *before* the inductiveness check, not after it. Likewise, safety is not needed for witness validity: an inductive annotation with `true` (instead of `false`) at FINAL is still a set of valid invariants.

---

## Change 1 — k≥2 invariants actually come through (commit + push)

All in `KInduction.java` unless stated otherwise.

1. **Phase logging.** Log the duration and outcome of each phase:
   - collecting candidates;
   - the Houdini/1-inductive attempt;
   - QE per head (with DAG size);
   - `isInductive` per step pair.

   Use one prefix, `KInduction witness:`, so the log classifier can tell which phase hit the timer. In `KInductionWorkerThread` also log k and the number of injected invariants when giving up.
2. **Fast path: nothing to compute.** If `mProvedK == 1` and no head or waypoint has an injected invariant, return all-`true` immediately: no `findScriptor`, no `isInductive`. This saves up to 2 s per verdict and no longer kills bitwuzla. Change 2 may add invariants to this case; then step 4 runs as usual.
3. **QF consecution check.** In `isInductive`, stop asserting `(exists freeVars. violation)`. Instead substitute the free term variables with fresh constants declared inside the `push`, as `KInductionQuery` does with `IndexedConstantVars`/`StepVars`. Skip pairs whose target invariant is `true`; the exception is a target of FINAL, whose invariant is `false`. This keeps every query quantifier-free for bitwuzla and z3.
4. **1-inductive strengthening before QE (Houdini).** For k≥2, try first an annotation without `noErrorWithinK`:
   - candidates per head/waypoint are the conjuncts of `J_h`, plus the supplier's current invariants (see Change 2's `collectInvariants` refresh);
   - FINAL = `false`.

   Run the k=1 step query (`KInductionQuery`, `Kind.STEP`, k=1, with these invariants). If it is UNSAT, the annotation proves safety and is 1-inductive, so use it with no QE. Otherwise fall back to the existing QE path.
5. **Partial results instead of nothing (Houdini fallback).** If the QE path fails (quantifier left, timer) or `isInductive` fails, do not return empty. Run Houdini on the conjuncts, with FINAL relaxed to `true`: drop conjuncts that some step pair does not preserve until the rest is inductive. Return what survives; it is a set of valid invariants, though not a safety proof. Reuse the conjunct and consecution logic of `TraceAbstraction/.../parallel/invariants/InductivenessChecker.java` where it fits; check whether it can be called with this system and script.
6. **Budget: raise it to 20 s (user request).**
   - Replace the hard-coded `WITNESS_TIMEOUT_MILLIS` (1500) / `WITNESS_GRACE_MILLIS` (500) in `KInductionWorkerThread` with a TraceAbstraction preference: label "K-induction witness timeout", **default 20000 ms**, added in `TraceAbstractionPreferenceInitializer` with its getter in `TAPreferences`. Keep the grace at 500 ms.
   - Set the same 20 s explicitly in the eight `svcomp-{Reach,Overflow}-{32,64}bit-Automizer_{Default,Bitvector}.epf`. Prove that the key is read: the log has to show the 20 s value.
   - Make the budget phase-aware: when the timer ends during QE, the Houdini result of step 5 on whatever exists still gets a short grace.
   - The fast path (step 2) and the QF check (step 3) keep the common k=1 case far below this budget, so the larger limit should only cost time where there is real work. Measure the SAFE wall time in the sweep anyway.

## Change 2 — enrich k=1 (and every) witness with the supplier's invariants (commit + push)

1. In `computeWitnessInvariants`, before building the annotation, call `collectInvariants()` once more. Then start from the **current** `mInjectedInvariants` conjoined with `mProofInvariants`, instead of the proof-time snapshot alone. By then the TA worker usually has submitted more interpolants, and `InvariantSupplier`/`InductivenessChecker` have proven some of them inductive.
2. The supplier's invariants are only trusted after the (now cheap, QF) `isInductive` check. On failure, Houdini (Change 1.5) prunes them, keeping the proof's `J` / `true` baseline. For k=1 the safety half needs nothing beyond `J_proof`, because the step case already showed it.
3. Waypoints: as now, they get invariants only for the check and are never reported.
4. Log the number of non-`true` invariants per witness (`KInduction witness: N of M head(s) non-trivial`).

## Change 3 — downstream drop points (commit + push)

1. **`KInductionWorkerThread.computeWitnessInvariantsWithin`:**
   - A head at several call sites (322-326): report the **disjunction** of the call sites' invariants at that location instead of giving up. Each call site's invariant holds there, so the disjunction does too.
   - An out-of-scope variable (327-332): drop only that head's invariant and keep the others. This is sound by the subset fact.
2. **`ParallelNwaCegarLoop.kInductionAnnotation` (643-668):**
   - A head that is not an ICFG loop location, or not a state of the program: skip that entry.
   - An ICFG loop location without a head (e.g. a loop removed by `LiveStates`): leave it unannotated.
   - Return null only if nothing is left.
   - Check that `TransformFloydHoareAnnotation.nwaToIcfg` and the assert-only `IcfgFloydHoareValidityCheck(…, MissingAnnotationBehaviour.IGNORE, …)` in `TraceAbstractionStarter` accept the partial map.
3. **An injected invariant that prints as nothing.** In `hardness/hardness_kloop_100_1loop_file-151`, `J = (<= 0 (div ~var_1_27~0 4294967296))` reaches "using the invariants … at 1 loop head" but yields no `InvariantResult`. Reproduce it locally, find where it vanishes (Term2Expression → Boogie2ACSL, or the `"1"`/`"true"` filter), and fix it if it is a real loss. It may legitimately be trivial for an unsigned variable; then leave it and note why.

---

## Verification

Build and run as the `ultimate-build-test` skill describes. Witness checks follow the `ultimate-witnesses` skill: `Ultimate.py --validate witness.yml`, where `Result: TRUE` means confirmed for a correctness witness.

1. **Inputs.** There is no local sv-benchmarks checkout. Download single tasks (`.yml` + `.i`) from `https://sv-comp.sosy-lab.org/2027/results/sv-benchmarks/c/<path>` into the scratchpad:
   - `hardness/hardness_operatoramount_amount100_file-18` (k=1, true; tests the fast path and Change 2)
   - `hardness/hardness_kloop_100_1loop_file-151` (k=1 with J; tests Change 3.3)
   - `eca-rers2012/Problem01_label14`, `eca-rers2012/Problem11_label33` (k=2)
   - `infeasible-control-flow/unreach_branch3` (k=2)
   - `nla-digbench-scaling/ps2-ll_unwindbound5`, `nla-digbench-scaling/bresenham-ll_valuebound100` (k=3, J)
   - `array-examples/data_structures_set_multi_proc_trivial_ground` (TA wins; regression check)
2. **Per program:** run with `svcomp-Reach-32bit-Automizer_Default.epf` and `--enable-assertions`. Check that:
   - the `KInduction witness:` phase lines appear;
   - `witness.yml` has non-empty `content` where expected;
   - the verdict time is not worse.

   Then validate each witness with `--validate`.
3. **After each change**, rerun the classifier from this investigation, which streams logs from the SV-COMP site or reads local logs. Run it over a local mini-sweep of about 100 KI-won TRUE tasks, mixing hardness, eca-rers2012, nla-digbench-scaling and combinations, with `TIMEOUT=600`. Compare:
   - the number of non-trivial witnesses;
   - the "without invariants" reasons;
   - the wall time of SAFE verdicts.

   Report the before and after numbers in each commit message.
4. Run the existing k-induction tests (`Library-KInductionTest`) and the witness regression test from 9d91ccc8c1.
