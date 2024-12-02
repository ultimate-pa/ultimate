package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.assertorders;

import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashTreeRelation;

/**
 * Assert statements in incremental order by their depth, and check after each step for satisfiability. E.g. first
 * assert all statements with depth 0, then assert all statements at depth 1, and so on.
 *
 * @author musab@informatik.uni-freiburg.de
 */
public class AssertOrderOutsideLoopFirst2<L extends IAction> implements IAssertOrder<L> {
	@Override
	public List<Set<Integer>> partitionTrace(final NestedWord<L> trace,
			final List<Object> controlConfigurationSequence) {
		final HashTreeRelation<Object, Integer> rwt =
				AssertOrderUtils.computeRelationWithTreeSetForTrace(0, trace.length(), controlConfigurationSequence);
		final Map<Integer, Set<Integer>> depth2Statements =
				AssertOrderUtils.partitionStatementsAccordingDepth(trace, rwt, controlConfigurationSequence);
		return depth2Statements.keySet().stream().sorted().map(depth2Statements::get).toList();
	}
}
