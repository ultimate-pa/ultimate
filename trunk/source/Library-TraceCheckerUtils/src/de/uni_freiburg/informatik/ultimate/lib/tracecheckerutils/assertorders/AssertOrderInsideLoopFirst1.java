package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.assertorders;

import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashTreeRelation;

/**
 * Assert statements in decremental order by their depth, and check after each step for satisfiability. E.g. first
 * assert all statements with depth max_depth, then assert all statements of depth max_depth - 1, and so on.
 *
 * @author musab@informatik.uni-freiburg.de
 */
public class AssertOrderInsideLoopFirst1<L extends IAction> extends AssertOrder<L> {
	@Override
	public List<Set<Integer>> partitionTrace(final NestedWord<L> trace,
			final List<Object> controlConfigurationSequence) {
		final HashTreeRelation<Object, Integer> rwt =
				computeRelationWithTreeSetForTrace(0, trace.length(), controlConfigurationSequence);
		final Map<Integer, Set<Integer>> depth2Statements =
				partitionStatementsAccordingDepth(trace, rwt, controlConfigurationSequence);
		return depth2Statements.keySet().stream().sorted((i1, i2) -> i2.compareTo(i1)).map(depth2Statements::get)
				.toList();
	}
}
