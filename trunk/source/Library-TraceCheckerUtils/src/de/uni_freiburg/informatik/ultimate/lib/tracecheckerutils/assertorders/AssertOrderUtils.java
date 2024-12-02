package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.assertorders;

import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashTreeRelation;

public class AssertOrderUtils {
	/**
	 * Returns a set of indices that represents all statements that is present in {@code trace}, but not in
	 * {@code statementIndices}.
	 */
	public static Set<Integer> getTraceDifference(final NestedWord<?> trace, final Set<Integer> statementIndices) {
		return IntStream.range(0, trace.length()).boxed().filter(x -> !statementIndices.contains(x))
				.collect(Collectors.toSet());
	}

	/**
	 *
	 * Partition the statements of the given trace according to their depth.
	 */
	public static <LETTER extends IAction, LOC> Map<Integer, Set<Integer>> partitionStatementsAccordingDepth(
			final NestedWord<LETTER> trace, final HashTreeRelation<LOC, Integer> rwt, final List<LOC> pps) {
		final Map<Integer, Set<Integer>> depth2Statements = new HashMap<>();

		dfsPartitionStatementsAccordingToDepth(0, trace.length(), 0, rwt, depth2Statements, pps);

		return depth2Statements;
	}

	/**
	 * Partition the statement positions between lowerIndex and upperIndex according to their depth. (See documentation
	 * for the meaning of 'depth'). The result is stored in the map 'depth2Statements'. The partitioning is done
	 * recursively.
	 */
	private static <LOC> void dfsPartitionStatementsAccordingToDepth(final Integer lowerIndex, final Integer upperIndex,
			final int depth, final HashTreeRelation<LOC, Integer> rwt,
			final Map<Integer, Set<Integer>> depth2Statements, final List<LOC> pps) {
		int i = lowerIndex;
		while (i < upperIndex) {
			// Is the current statement a loop entry?
			if (rwt.getImage(pps.get(i)).size() >= 2 && rwt.getImage(pps.get(i)).higher(i) != null
					&& rwt.getImage(pps.get(i)).higher(i) < upperIndex) {
				// the new upper index is the last occurrence of the same location
				final int newUpperIndex = rwt.getImage(pps.get(i)).lower(upperIndex);
				addStmtPositionToDepth(depth + 1, depth2Statements, i);
				// we consider the subtrace from i+1 to newUpperIndex as a loop
				// and apply the partitioning recursively on the subtrace
				dfsPartitionStatementsAccordingToDepth(i + 1, newUpperIndex, depth + 1, rwt, depth2Statements, pps);
				// continue at the position after the loop
				i = newUpperIndex;
			} else {
				addStmtPositionToDepth(depth, depth2Statements, i);
				i++;
			}
		}
	}

	/**
	 * Add the position 'stmtPos' to the map 'depth2Statements' where the key is the given 'depth'.
	 */
	private static void addStmtPositionToDepth(final int depth, final Map<Integer, Set<Integer>> depth2Statements,
			final int stmtPos) {
		if (depth2Statements.containsKey(depth)) {
			depth2Statements.get(depth).add(stmtPos);
		} else {
			final Set<Integer> s = new HashSet<>();
			s.add(stmtPos);
			depth2Statements.put(depth, s);
		}
	}

	/**
	 * TODO(Betim): DOcumentation!
	 */
	public static <LOC> HashTreeRelation<LOC, Integer> computeRelationWithTreeSetForTrace(final int lowerIndex,
			final int upperIndex, final List<LOC> pps) {
		final HashTreeRelation<LOC, Integer> rwt = new HashTreeRelation<>();
		for (int i = lowerIndex; i <= upperIndex; i++) {
			rwt.addPair(pps.get(i), i);
		}
		return rwt;
	}
}
