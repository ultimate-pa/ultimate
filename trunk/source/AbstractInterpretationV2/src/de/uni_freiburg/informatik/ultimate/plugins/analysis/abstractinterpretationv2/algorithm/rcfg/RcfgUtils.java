package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.rcfg;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.List;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Summary;

/**
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public final class RcfgUtils {

	private RcfgUtils() {
	}

	public static boolean isAllowedReturn(final CodeBlock current, final CodeBlock currentScope) {
		if (currentScope == null) {
			return false;
		}
		if (current instanceof Return) {
			final Return currReturn = (Return) current;
			assert currentScope instanceof Call;
			return currReturn.getCorrespondingCall().equals(currentScope);
		}
		return false;
	}

	public static boolean isValidSuccessor(final IcfgEdge successor, final CodeBlock lastCall) {
		if (!(successor instanceof CodeBlock)) {
			return false;
		}
		final CodeBlock cbSucc = (CodeBlock) successor;
		return !(cbSucc instanceof Return) || RcfgUtils.isAllowedReturn(cbSucc, lastCall);
	}

	public static <E extends IcfgEdge> Collection<CodeBlock> getValidCodeBlocks(final Collection<E> candidates,
			final CodeBlock lastCall) {
		if (candidates == null) {
			return Collections.emptyList();
		}
		final List<CodeBlock> rtr = new ArrayList<>(candidates.size());
		for (final IcfgEdge successor : candidates) {
			if (!RcfgUtils.isValidSuccessor(successor, lastCall)) {
				continue;
			}
			rtr.add((CodeBlock) successor);
		}
		return rtr;
	}

	public static boolean isSummaryWithImplementation(final IcfgEdge edge) {
		if (edge instanceof Summary) {
			final Summary sum = (Summary) edge;
			return sum.calledProcedureHasImplementation();
		}
		return false;
	}

	/**
	 * @return true iff <code>action</code> is a summary for <code>call</code>
	 */
	public static boolean isSummaryForCall(final CodeBlock action, final CodeBlock possibleCall) {
		if (possibleCall instanceof Call && action instanceof Summary) {
			final Call call = (Call) possibleCall;
			final Summary summary = (Summary) action;
			return summary.getCallStatement() == call.getCallStatement();
		}
		return false;
	}

	public static Collection<IcfgEdge> getInitialEdges(final IIcfg<?> icfg) {
		return icfg.getInitialNodes().stream().flatMap(a -> a.getOutgoingEdges().stream()).collect(Collectors.toSet());
	}

	public static Collection<CodeBlock> getInitialCodeblocks(final IIcfg<?> icfg) {
		final Collection<IcfgEdge> initialEdges = getInitialEdges(icfg);
		assert initialEdges.stream().allMatch(a -> a instanceof CodeBlock);
		return initialEdges.stream().map(a -> (CodeBlock) a).collect(Collectors.toSet());
	}

}
