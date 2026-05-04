package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent;

import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgForkTransitionThreadCurrent;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgJoinTransitionThreadCurrent;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.IInterference;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.InterferenceCollection;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.setup.ThreadActivityPreanalysis;
import de.uni_freiburg.informatik.ultimate.lib.sifa.domain.IDomain;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;

/**
 * Soundness-retaining optimizations
 */
final class Optimizations {

	static boolean trivialState(final IPredicate state, final InterferenceCollection interferences) {
		return interferences.isEmpty() || SmtUtils.isTrueLiteral(state.getFormula())
				|| SmtUtils.isFalseLiteral(state.getFormula());
	}

	static boolean noGrowth(final IDomain domain, final IPredicate candidate, final IPredicate current) {
		return domain.isSubsetEq(candidate, current).isTrueForAbstraction();
	}

	static boolean roundConverged(final boolean changed, final IDomain domain, final IPredicate current,
			final IPredicate roundStart) {
		return !changed || noGrowth(domain, current, roundStart);
	}

	static boolean localTransition(final IIcfgTransition<IcfgLocation> transition) {
		return !isForkOrJoin(transition) && !touchesGlobals(transition);
	}

	static List<IInterference> filterApplicable(final ThreadAnalysisContext ctx, final IcfgLocation location,
			final ThreadActivityPreanalysis preanalysis) {
		return ctx.applicableInterferencesByLocation().computeIfAbsent(location,
				loc -> computeApplicable(ctx, loc, preanalysis));
	}

	private static List<IInterference> computeApplicable(final ThreadAnalysisContext ctx, final IcfgLocation location,
			final ThreadActivityPreanalysis preanalysis) {
		final List<IInterference> result = new ArrayList<>();
		final String threadId = ctx.threadId();
		final boolean includeSelf = ctx.includeSelfInterference();
		for (final String otherId : ctx.sortedInterferenceThreadIds()) {
			if (otherId.equals(threadId) && !includeSelf) {
				continue; // self-interference
			}
			if (!preanalysis.mayBeActiveAt(location, otherId)) {
				continue; // known inactive
			}
			if (preanalysis.isDefinitelyJoinedAt(location, otherId)) {
				continue; // definitely joined before this location
			}
			final IInterference itf = ctx.interferences().getInterferenceForThread(otherId);
			if (itf == null) {
				continue; // trivial interference
			}
			result.add(itf);
		}
		return List.copyOf(result);
	}

	private static boolean isForkOrJoin(final IIcfgTransition<IcfgLocation> transition) {
		return transition instanceof IIcfgForkTransitionThreadCurrent<?>
				|| transition instanceof IIcfgJoinTransitionThreadCurrent<?>;
	}

	private static boolean touchesGlobals(final IIcfgTransition<IcfgLocation> transition) {
		final var tf = transition.getTransformula();
		if (tf == null) {
			return false;
		}
		return tf.getInVars().keySet().stream().anyMatch(v -> v.isGlobal())
				|| tf.getOutVars().keySet().stream().anyMatch(v -> v.isGlobal());
	}

	private Optimizations() {
	}
}
