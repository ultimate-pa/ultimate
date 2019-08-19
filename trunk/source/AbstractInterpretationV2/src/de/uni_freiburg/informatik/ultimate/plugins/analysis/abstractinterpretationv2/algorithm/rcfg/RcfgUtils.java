package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.rcfg;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.List;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgCallTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgReturnTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Summary;

/**
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public final class RcfgUtils {

	private RcfgUtils() {
	}

	public static boolean isAllowedReturn(final IIcfgReturnTransition<?, ?> current,
			final IIcfgTransition<?> currentScope) {
		if (currentScope == null) {
			return false;
		}
		assert currentScope instanceof IIcfgCallTransition<?>;
		return current.getCorrespondingCall().equals(currentScope);

	}

	public static boolean isValidSuccessor(final IcfgEdge successor, final IcfgEdge lastCall) {
		return !(successor instanceof IIcfgReturnTransition<?, ?>)
				|| RcfgUtils.isAllowedReturn((IIcfgReturnTransition<?, ?>) successor, lastCall);
	}

	public static <E extends IcfgEdge> Collection<IcfgEdge> getValidCodeBlocks(final Collection<E> candidates,
			final E lastCall) {
		if (candidates == null) {
			return Collections.emptyList();
		}
		final List<IcfgEdge> rtr = new ArrayList<>(candidates.size());
		for (final IcfgEdge successor : candidates) {
			if (!RcfgUtils.isValidSuccessor(successor, lastCall)) {
				continue;
			}
			rtr.add(successor);
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
	public static boolean isSummaryForCall(final IcfgEdge action, final IcfgEdge possibleCall) {
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
