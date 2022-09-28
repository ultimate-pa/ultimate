package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.concurrent;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.PriorityQueue;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.DisjunctiveAbstractState;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractState;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

public class InterferenceUtils {
	private InterferenceUtils() {
	}

	// TODO: Does this also work for edge cases (top/bottom states)?
	public static <STATE extends IAbstractState<STATE>> DisjunctiveAbstractState<STATE> computeStateWithInterferences(
			final DisjunctiveAbstractState<STATE> state, final DisjunctiveAbstractState<STATE> interferingState) {
		final Set<IProgramVarOrConst> sharedVars =
				DataStructureUtils.intersection(interferingState.getVariables(), state.getVariables());
		final DisjunctiveAbstractState<STATE> unionOnSharedVars =
				keepVariables(state, sharedVars).union(keepVariables(interferingState, sharedVars));
		return state.patch(unionOnSharedVars);
	}

	private static <STATE extends IAbstractState<STATE>> DisjunctiveAbstractState<STATE>
			keepVariables(final DisjunctiveAbstractState<STATE> state, final Set<IProgramVarOrConst> vars) {
		final Set<IProgramVarOrConst> varsToRemove = DataStructureUtils.difference(state.getVariables(), vars);
		return state.removeVariables(varsToRemove);
	}

	private static HashRelation<String, String> getForkRelation(final IIcfg<?> icfg) {
		final var forks = icfg.getCfgSmtToolkit().getConcurrencyInformation().getThreadInstanceMap().keySet();
		final HashRelation<String, String> result = new HashRelation<>();
		forks.forEach(x -> result.addPair(x.getPrecedingProcedure(), x.getNameOfForkedProcedure()));
		return result;
	}

	// TODO: This seems rather inefficient and complicated. Can we do better?
	public static List<String> getTopologicalProcedureOrder(final IIcfg<?> icfg) {
		final Set<String> procedures = icfg.getProcedureEntryNodes().keySet();
		final Map<String, Integer> inGrad = new HashMap<>();
		for (final String procedure : procedures) {
			inGrad.put(procedure, 0);
		}

		final HashRelation<String, String> forks = getForkRelation(icfg);
		for (final var entry : forks.entrySet()) {
			for (final String forked : entry.getValue()) {
				inGrad.put(forked, inGrad.get(forked) + 1);
			}
		}

		final PriorityQueue<Pair<String, Integer>> pQueue =
				new PriorityQueue<>((x, y) -> x.getSecond() - y.getSecond());
		inGrad.forEach((k, v) -> pQueue.add(new Pair<>(k, v)));

		final Set<String> visited = new HashSet<>();
		final List<String> result = new ArrayList<>();
		while (!DataStructureUtils.difference(procedures, visited).isEmpty()) {
			final Pair<String, Integer> currentItem = pQueue.poll();
			if (currentItem.getSecond() == 0) {
				final String key = currentItem.getFirst();
				if (!visited.contains(key)) {
					result.add(key);
					visited.add(key);

					for (final String forked : forks.getImage(key)) {
						if (inGrad.get(forked) > 0) {
							inGrad.put(forked, inGrad.get(forked) - 1);
							pQueue.add(new Pair<>(forked, inGrad.get(forked)));
						}
					}
				}
				continue;
			}

			// cycle -> add others in arbitrary order
			for (final String procedure : DataStructureUtils.difference(procedures, visited)) {
				result.add(procedure);
			}
			break;
		}
		return result;
	}
}
