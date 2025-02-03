package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.assertorders;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.function.Predicate;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.Counterexample;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

/**
 *
 * @param <L>
 */
public class AssertOrderRelatedVariables<L extends IAction> implements IAssertOrder<L> {
	private final Predicate<L> mInitialActions;
	private final int mMaxPartitions;

	public AssertOrderRelatedVariables(final Predicate<L> initialActions, final int maxPartitions) {
		mInitialActions = initialActions;
		mMaxPartitions = maxPartitions;
	}

	@Override
	public List<Set<Integer>> partition(final Counterexample<L> counterexample) {
		final HashRelation<L, Integer> counterexampleIndices = new HashRelation<>();
		final HashRelation<IProgramVar, L> variableOccurence = new HashRelation<>();
		for (int i = 0; i < counterexample.length(); i++) {
			final L action = counterexample.getWord().getSymbol(i);
			counterexampleIndices.addPair(action, i);
			for (final IProgramVar pv : TransFormula.collectAllProgramVars(action.getTransformula())) {
				variableOccurence.addPair(pv, action);
			}
		}
		final Set<L> visitedActions = new HashSet<>();
		final List<Set<Integer>> result = new ArrayList<>(mMaxPartitions);
		List<L> currentActions = counterexample.getWord().asList().stream().filter(mInitialActions).toList();
		for (int i = 0; i < mMaxPartitions; i++) {
			if (currentActions.isEmpty()) {
				break;
			}
			visitedActions.addAll(currentActions);
			final Set<IProgramVar> curentVariables = new HashSet<>();
			final Set<Integer> currentIndices = new HashSet<>();
			for (final L action : currentActions) {
				currentIndices.addAll(counterexampleIndices.getImage(action));
				curentVariables.addAll(TransFormula.collectAllProgramVars(action.getTransformula()));
			}
			result.add(currentIndices);
			currentActions = curentVariables.stream().flatMap(x -> variableOccurence.getImage(x).stream())
					.filter(x -> !visitedActions.contains(x)).toList();
		}
		// Add all the remaining actions
		result.add(counterexample.getWord().asList().stream().filter(x -> !visitedActions.contains(x))
				.flatMap(x -> counterexampleIndices.getImage(x).stream()).collect(Collectors.toSet()));
		return result;
	}
}
