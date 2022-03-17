# Ultimate GemCutter

This README describes settings and inputs specific to Ultimate GemCutter.
For general information on the Ultimate tools and how to use them, refer to <https://github.com/ultimate-pa/ultimate/blob/dev/releaseScripts/default/adds/README>.

Settings for Ultimate can be specified in two ways: via a command line parameter, or by writing them to an `.epf` file and passing this file with the command line parameter `-s`.
The following describes settings specific to Ultimate GemCutter.

## Commutativity

### Conditional (Proof-Sensitive) Commutativity

*Proof-sensitive commutativity*, also called *conditional commutativity*, refers to the fact that proof assertions are used to determine if statements commute (in states where such a proof assertions hold).

* Possible Values: `true` (proof-sensitive commutativity is used), `false` (proof assertions are ignored when checking commutativity)
* Default Value: `true`
* Command Line: `--traceabstraction.use.conditional.por.in.concurrent.analysis <arg>`
* Settings Directive:
  ```
  /instance/de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction/Use\ conditional\ POR\ in\ concurrent\ analysis=<arg>
  ```

### Symmetric Commutativity

GemCutter can use classical (symmetric) commutativity (`a` and `b` commute iff `ab` behaves as `ba`), or semi-commutativity.
In the latter case, Mazurkiewicz equivalence degenerates to a pre-order.

* Possible Values: `true` (only symmetric commutativity is used), `false` (semi-commutativity is used)
* Default Value: `false`
* Command Line: `--traceabstraction.limit.por.to.symmetric.independence.in.concurrent.analysis <arg>`
* Settings Directive:
  ```
  /instance/de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction/Limit\ POR\ to\ symmetric\ independence\ in\ concurrent\ analysis=<arg>
  ```

## Preference Orders

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

* Possible Values: `NONE` (no reduction is applied), `SLEEP_DELAY_SET`, `SLEEP_NEW_STATES`, `PERSISTENT_SETS`, `PERSISTENT_SLEEP_DELAY_SET`, `PERSISTENT_SLEEP_DELAY_SET_FIXEDORDER`, `PERSISTENT_SLEEP_NEW_STATES`, `PERSISTENT_SLEEP_NEW_STATES_FIXEDORDER`
* Default Value: `NONE`
* Command Line: `--traceabstraction.partial.order.reduction.in.concurrent.analysis <arg>`
* Settings Directive:
  ```
  /instance/de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction/Partial\ Order\ Reduction\ in\ concurrent\ analysis=<arg>
  ```

We implement two variants of sleep sets:
* `SLEEP_NEW_STATES` implements a language-minimal reduction (in case of symmetric commutativity), and may duplicate states to achieve this.
* `SLEEP_DELAY_SET` does not guarantee a minimal reduction, but ensures that states are not duplicated during the reduction. This is not recommended and may be removed.

For the combination of sleep sets and persistent sets, there are again two variants:
* `FIXEDORDER` indicates that the specified preference order (see above) is strictly adhered to when computing the reduction.
* If the suffix `FIXEDORDER` is missing, the preference order may be modified when this allows for more aggressive state pruning by persistent sets.


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