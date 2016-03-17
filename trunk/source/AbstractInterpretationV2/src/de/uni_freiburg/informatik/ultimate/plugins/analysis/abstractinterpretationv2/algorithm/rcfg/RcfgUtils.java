package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.rcfg;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGEdge;
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
			Return currReturn = (Return) current;
			assert currentScope instanceof Call;
			return currReturn.getCorrespondingCall().equals(currentScope);
		}
		return false;
	}

	public static boolean isValidSuccessor(final RCFGEdge successor, final CodeBlock lastCall) {
		if (!(successor instanceof CodeBlock)) {
			return false;
		}

		final CodeBlock cbSucc = (CodeBlock) successor;
		if (cbSucc instanceof Return) {
			if (!RcfgUtils.isAllowedReturn(cbSucc, lastCall)) {
				return false;
			}
		}
		return true;
	}

	public static <E extends RCFGEdge> Collection<CodeBlock> getValidCodeBlocks(final Collection<E> candidates,
			final CodeBlock lastCall) {
		if (candidates == null) {
			return Collections.emptyList();
		}
		final List<CodeBlock> rtr = new ArrayList<>(candidates.size());
		for (final RCFGEdge successor : candidates) {
			if (!RcfgUtils.isValidSuccessor(successor, lastCall)) {
				continue;
			}
			rtr.add((CodeBlock) successor);
		}
		return rtr;
	}

	public static boolean isSummaryWithImplementation(final RCFGEdge edge) {
		if (edge instanceof Summary) {
			final Summary sum = (Summary) edge;
			return sum.calledProcedureHasImplementation();
		}
		return false;
	}

	/**
	 * @return true iff <code>action</code> is a summary for <code>call</code>
	 */
	public static boolean isSummaryForCall(CodeBlock action, CodeBlock possibleCall) {
		if (possibleCall instanceof Call && action instanceof Summary) {
			final Call call = (Call) possibleCall;
			final Summary summary = (Summary) action;
			return summary.getCallStatement() == call.getCallStatement();
		}
		return false;
	}

}
