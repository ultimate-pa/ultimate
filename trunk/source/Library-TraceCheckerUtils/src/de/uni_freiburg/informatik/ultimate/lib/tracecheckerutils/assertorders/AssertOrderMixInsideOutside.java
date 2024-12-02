package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.assertorders;

import java.util.ArrayList;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashTreeRelation;

/**
 * Assert the statements with the highest depth and lowest depth in alternating order.
 *
 * @author musab@informatik.uni-freiburg.de
 */
public class AssertOrderMixInsideOutside<L extends IAction> implements IAssertOrder<L> {
	@Override
	public List<Set<Integer>> partitionTrace(final NestedWord<L> trace,
			final List<Object> controlConfigurationSequence) {
		final HashTreeRelation<Object, Integer> rwt =
				AssertOrderUtils.computeRelationWithTreeSetForTrace(0, trace.length(), controlConfigurationSequence);
		final Map<Integer, Set<Integer>> depth2Statements =
				AssertOrderUtils.partitionStatementsAccordingDepth(trace, rwt, controlConfigurationSequence);
		final LinkedList<Integer> depthAsQueue =
				depth2Statements.keySet().stream().sorted().collect(Collectors.toCollection(LinkedList::new));
		final List<Set<Integer>> result = new ArrayList<>(depth2Statements.size());
		boolean removeFirst = true;
		while (!depthAsQueue.isEmpty()) {
			final int currentDepth;
			if (removeFirst) {
				currentDepth = depthAsQueue.removeFirst();
			} else {
				currentDepth = depthAsQueue.removeLast();
			}
			removeFirst = !removeFirst;
			result.add(depth2Statements.get(currentDepth));
		}
		return result;
	}
}
