package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.assertorders;

import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.Counterexample;

public class AssertOrderWitnessSimple<L extends IAction> implements IAssertOrder<L> {
	@Override
	public List<Set<Integer>> partition(final Counterexample<L> counterexample) {
		final NestedWord<L> trace = counterexample.getWord();
		final Set<Integer> witnessActions = IntStream.range(0, trace.length())
				.filter(x -> AssertOrderUtils.isWitnessAction(trace.getSymbol(x))).boxed().collect(Collectors.toSet());
		final Set<Integer> otherActions = AssertOrderUtils.getTraceDifference(trace, witnessActions);
		if (witnessActions.isEmpty()) {
			return List.of(otherActions);
		}
		return List.of(witnessActions, otherActions);
	}
}
