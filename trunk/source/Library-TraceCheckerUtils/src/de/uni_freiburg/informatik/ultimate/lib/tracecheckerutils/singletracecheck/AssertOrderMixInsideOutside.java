package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.singletracecheck;

import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashTreeRelation;

/**
 * Assert the statements with the highest depth and lowest depth in alternating order.
 *
 * @author musab@informatik.uni-freiburg.de
 */
public class AssertOrderMixInsideOutside<L extends IAction> extends AssertOrder<L> {
	@Override
	public List<Set<Integer>> partitionTrace(final NestedWord<L> trace,
			final List<Object> controlConfigurationSequence) {
		final HashTreeRelation<Object, Integer> rwt =
				computeRelationWithTreeSetForTrace(0, trace.length(), controlConfigurationSequence);
		final Map<Integer, Set<Integer>> depth2Statements =
				partitionStatementsAccordingDepth(trace, rwt, controlConfigurationSequence);
		final LinkedList<Integer> depthAsQueue = new LinkedList<>(depth2Statements.keySet());
		Collections.sort(depthAsQueue);
		final List<Set<Integer>> result = new ArrayList<>(depth2Statements.size());
		boolean removeFirst = true;
		while (!depthAsQueue.isEmpty()) {
			int currentDepth = 0;
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
