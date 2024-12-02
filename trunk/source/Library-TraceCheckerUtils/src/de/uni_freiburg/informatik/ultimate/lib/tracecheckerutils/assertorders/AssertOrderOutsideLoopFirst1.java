package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.assertorders;

import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashTreeRelation;

/**
 * First, assert all statements which don't occur inside of a loop. Then, check for satisfiability. If the result of the
 * satisfiability check is not unsatisfiable, then assert the rest of the statements, and return the result of the
 * unsatisfiability check.
 *
 * @author musab@informatik.uni-freiburg.de
 */
public class AssertOrderOutsideLoopFirst1<L extends IAction> implements IAssertOrder<L> {
	@Override
	public List<Set<Integer>> partitionTrace(final NestedWord<L> trace,
			final List<Object> controlConfigurationSequence) {
		final HashTreeRelation<Object, Integer> rwt =
				AssertOrderUtils.computeRelationWithTreeSetForTrace(0, trace.length(), controlConfigurationSequence);
		final Map<Integer, Set<Integer>> depth2Statements =
				AssertOrderUtils.partitionStatementsAccordingDepth(trace, rwt, controlConfigurationSequence);
		// Statements outside of a loop have depth 0.
		// First, annotate and assert the statements, which doesn't occur within a loop
		final Set<Integer> stmtsOutsideOfLoop = depth2Statements.get(0);
		if (stmtsOutsideOfLoop.size() == trace.length()) {
			return List.of(stmtsOutsideOfLoop);
		}
		final Set<Integer> stmtsWithinLoop = AssertOrderUtils.getTraceDifference(trace, stmtsOutsideOfLoop);
		return List.of(stmtsOutsideOfLoop, stmtsWithinLoop);
	}
}
