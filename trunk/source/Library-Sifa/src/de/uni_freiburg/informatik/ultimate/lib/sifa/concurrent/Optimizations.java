package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent;

import java.util.LinkedHashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgForkTransitionThreadCurrent;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgJoinTransitionThreadCurrent;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.bucketdomain.AbstractLocationPartitionedPredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.IInterference;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.setup.ThreadActivityPreanalysis;
import de.uni_freiburg.informatik.ultimate.lib.sifa.domain.IDomain;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;

/**
 * Soundness-retaining optimizations
 */
final class Optimizations {

	static boolean trivialState(final IPredicate state, final IInterference interference) {
		return interference == null || interference.isEmpty()
				|| (!(state instanceof AbstractLocationPartitionedPredicate) && SmtUtils.isTrueLiteral(state.getFormula()))
				|| (!(state instanceof AbstractLocationPartitionedPredicate) && SmtUtils.isFalseLiteral(state.getFormula()));
	}

	static boolean noGrowth(final IDomain domain, final IPredicate candidate, final IPredicate current) {
		return candidate == current || domain.isSubsetEq(candidate, current).isTrueForAbstraction();
	}

	static boolean roundConverged(final boolean changed, final IDomain domain, final IPredicate current,
			final IPredicate roundStart) {
		return !changed || noGrowth(domain, current, roundStart);
	}

	static boolean localTransition(final IIcfgTransition<IcfgLocation> transition) {
		return !isForkOrJoin(transition) && !touchesGlobals(transition);
	}

	static Set<String> filterApplicable(final ThreadAnalysisContext ctx, final IcfgLocation location,
			final ThreadActivityPreanalysis preanalysis) {
		return ctx.activeThreadIdsByLocation().computeIfAbsent(location,
				loc -> computeApplicable(ctx, loc, preanalysis));
	}

	private static Set<String> computeApplicable(final ThreadAnalysisContext ctx, final IcfgLocation location,
			final ThreadActivityPreanalysis preanalysis) {
		final Set<String> result = new LinkedHashSet<>();
		final String threadId = ctx.threadId();
		final boolean includeSelf = ctx.includeSelfInterference();
		for (final String otherId : ctx.sortedInterferenceThreadIds()) {
			if (otherId.equals(threadId) && !includeSelf) {
				continue;
			}
			if (!preanalysis.mayBeActiveAt(location, otherId)) {
				continue;
			}
			if (preanalysis.isDefinitelyJoinedAt(location, otherId)) {
				continue;
			}
			result.add(otherId);
		}
		return Set.copyOf(result);
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
