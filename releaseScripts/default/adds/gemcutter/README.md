# Ultimate GemCutter

This README describes settings and inputs specific to Ultimate GemCutter.
For general information on the Ultimate tools and how to use them, refer to <https://github.com/ultimate-pa/ultimate/blob/dev/releaseScripts/default/adds/README>.

Settings for Ultimate can be specified in two ways: via a command line parameter, or by writing them to an `.epf` file and passing this file with the command line parameter `-s`.
The following describes settings specific to Ultimate GemCutter.



## Commutativity

The concept of commutativity determines which statements can be swapped.
In GemCutter, this concept is typically referred to as "independence".


### Number of Commutativity Relations

GemCutter can use one (standard) or _several_ (stratified) commutativity relations.
See [POPL23] for details.

* Possible Values: Any integer greater or equal to `1`
* Default Value: `1`
* Command Line: `--traceabstraction.number.of.independence.relations.to.use.for.por <arg>`
* Settings Directive:
  ```
  /instance/de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction/Number\ of\ independence\ relations\ to\ use\ for\ POR=<arg>
  ```

Unless otherwise noted, the following settings for commutativity relations can be specified for each relation separately.
The command line flags and settings directives below always refer to the first relation;
for other relations, append `.<i>` to the command line flag, resp. `\ #` to the settings directive key.


### Semi-Commutativity

GemCutter can use classical (symmetric) commutativity (`a` and `b` commute iff `ab` behaves as `ba`), or semi-commutativity (`a` semi-commutes against `b` if all behaviours of `ab` are also behaviours of `ba`).
In the latter case, Mazurkiewicz equivalence degenerates to a pre-order.
Enabling semi-commutativity typically brings performance benefits at no cost.

* Possible Values: `true` (semi-commutativity is used), `false` (only symmetric commutativity is used)
* Default Value: `true`
* Command Line: `--traceabstraction.use.semi.commutativity.for.por.in.concurrent.analysis <arg>`
* Settings Directive:
  ```
  /instance/de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction/Use\ semi-commutativity\ for\ POR\ in\ concurrent\ analysis=<arg>
  ```


### Conditional (Proof-Sensitive) Commutativity

*Conditional commutativity* refers to the fact that proof assertions are used to determine if statements commute (in states where such an assertion is proven to hold).

In particular, GemCutter supports two variants:
In *proof-sensitive* commutativity (see [PLDI22]), only the assertions of infeasibility proofs for programs interleavings are used for this purpose.
In *counterexample-guided* commutativity (see [CAV25]), suitable commutativity conditions are generated and proven in a targeted manner.
To enable the latter, see the setting further below.

* Possible Values: `true` (conditional commutativity is used), `false` (proof assertions are ignored when checking commutativity)
* Default Value: `true`
* Command Line: `--traceabstraction.use.conditional.por.in.concurrent.analysis <arg>`
* Settings Directive:
  ```
  /instance/de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction/Use\ conditional\ POR\ in\ concurrent\ analysis=<arg>
  ```


### Abstract Commutativity

*Abstract commutativity* allows other notions of commutativity to be used than those based on the concrete semantics of program instructions.
See [POPL23] for details.

* Possible Values: `NONE` (concrete commutativity is used), `VARIABLES_GLOBAL` (abstract commutativity based on projection to the proof is used)
* Default Value: `NONE`
* Command Line: `--traceabstraction.abstraction.used.for.commutativity.in.por <arg>`
* Settings Directive:
  ```
  /instance/de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction/Abstraction\ used\ for\ commutativity\ in\ POR=<arg>
  ```


### Syntactic vs Semantic Commutativity

For a precise check whether two statements commute, an SMT solver is needed.
Sometimes, it can be beneficial to avoid this costly SMT call and use a conservative syntactic approximation instead.

* Possible Values: `SYNTACTIC` (use the approximation only), `SEMANTIC` (use the SMT solver if the approximation is not sufficient)
* Default Value: `SEMANTIC`
* Command Line: `--traceabstraction.independence.relation.used.for.POR.in.concurrent.analysis <arg>`
* Settings Directive:
  ```
  /instance/de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction/Independence\ relation\ used\ for\ POR\ in\ concurrent\ analysis=<arg>
  ```


### SMT Solver for Independence

Different SMT solvers can be used to check independence of statements.

* Possible Values: `Z3`, `BITWUZLA`, `MATHSAT`, `SMTINTERPOL`, `PRINCESS`
* Default Value: `Z3`
* Command Line: `--traceabstraction.smt.solver.used.for.commutativity.in.por <arg>`
* Settings Directive:
  ```
  /instance/de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction/SMT\ solver\ used\ for\ commutativity\ in\ POR=<arg>
  ```

Note that the SMT solver is shared between all relations that need one (see previous setting for relations that do not need it), so the settings should coincide.


### SMT Timeout for Independence

The timeout for SMT independence checks can be changed. If no answer is reached before the timeout, GemCutter conservatively assumes the statements do not commute.

* Possible Values: an integer value indicating the timeout in ms
* Default Value: `1000`
* Command Line: `--traceabstraction.smt.solver.timeout.for.commutativity.in.POR.in.ms <arg>`
* Settings Directive:
  ```
  /instance/de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction/SMT\ solver\ timeout\ used\ for\ commutativity\ in\ POR\ (in\ ms)=<arg>`
  ```

As with the previous setting, all relations share the same timeout.


### Commutativity Condition Synthesis

This setting controls counterexample-guided commutativity (see above for a brief explanation).
For more information, see [CAV25].

* Possible Values: `NONE` (disables counterexample-guided commutativity), `SUFFICIENT` (generates sufficient but not always necessary conditions), `SUFFICIENT_WITH_CONTEXT` (ensures the sufficient conditions are consistent with known assertions), `NECESSARY_AND_SUFFICIENT` (generates the weakest commutativity conditions).
* Default Value: `NONE`
* Command Line: `--traceabstraction.commutativity.condition.synthesis <arg>`
* Settings Directive:
  ```
  /instance/de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction/Commutativity\ condition\ synthesis=<arg>
  ```

This setting can only be used if there is only one commutativity relation and it does not use abstract commutativity.



## Preference Orders

A preference order determines which representatives are selected (wrt. the equivalence relation / preorder induced by commutativity).


### Type of Preference Order

GemCutter currently supports a limited array of preference orders.

* Possible Values: `BY_SERIAL_NUMBER` (approximates sequential composition), `PSEUDO_LOCKSTEP` (approximates lockstep), `RANDOM` (randomized with a fixed seed, see below), `POSITIONAL_RANDOM` (positional randomized order with a fixed seed, see below), `LOOP_LOCKSTEP` (aims to context switch after a thread has completed an entire iteration of a loop)
* Default Value: `BY_SERIAL_NUMBER`
* Command Line: `--traceabstraction.dfs.order.used.in.por <arg>`
* Settings Directive:
  ```
  /instance/de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction/DFS\ Order\ used\ in\ POR=<arg>
  ```


### Random Order Seed

In case a (positional or non-positional) randomized preference order is used, fixes a seed value for the random generator to allow reproducibility.

* Possible Values: Any 32bit integer value
* Default Value: `0`
* Command Line: `--traceabstraction.random.seed.used.by.por.dfs.order <arg>`
* Settings Directive:
  ```
  /instance/de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction/Random\ seed\ used\ by\ POR\ DFS\ order=<arg>
  ```



## Reduction Algorithms

GemCutter supports different combinations of sleep set and persistent set reduction algorithms.

* Possible Values: `NONE` (no reduction is applied), `SLEEP_NEW_STATES`, `PERSISTENT_SETS`, `PERSISTENT_SLEEP_NEW_STATES`
* Default Value: `NONE`
* Command Line: `--traceabstraction.partial.order.reduction.in.concurrent.analysis <arg>`
* Settings Directive:
  ```
  /instance/de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction/Partial\ Order\ Reduction\ in\ concurrent\ analysis=<arg>
  ```



## CEGAR Loops

GemCutter can split the verification of a program across multiple CEGAR loops.

* Possible Values: `ONLY_ONE_CEGAR`, `ONE_CEGAR_PER_THREAD_INSTANCE`, `ONE_CEGAR_PER_ERROR_LOCATION`
* Default Value: `ONLY_ONE_CEGAR`
* Command Line: `--traceabstraction.cegar.restart.behaviour <arg>`
* Settings Directive:
  ```
  /instance/de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction/CEGAR\ restart\ behaviour=<arg>
  ```

When verifying a program with `assert` statements in multiple threads while using persistent set reduction, we recommend `ONE_CEGAR_PER_THREAD_INSTANCE`.



## References
- [PLDI22] Farzan, Klumpp and Podelski: _Sound sequentialization for concurrent program verification_ (<https://doi.org/10.1145/3519939.3523727>)
- [POPL23] Farzan, Klumpp and Podelski: _Stratified Commutativity in Verification Algorithms for Concurrent Programs_ (<https://doi.org/10.1145/3571242>)
- [CAV25] Ebbinghaus, Klumpp and Podelski: _Counterexample-Guided Commutativity_ (<https://doi.org/10.1007/978-3-031-98682-6_18>)

