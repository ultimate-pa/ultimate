package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgForkTransitionThreadCurrent;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgJoinTransitionThreadCurrent;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgJoinTransitionThreadOther;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.primedFormulas.RelationalPredicatePostcondition;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.primedFormulas.RelationalPredicatePostcondition.PreparedRelation;
import de.uni_freiburg.informatik.ultimate.lib.sifa.domain.IDomain;
import de.uni_freiburg.informatik.ultimate.lib.sifa.statistics.SifaStats;
import de.uni_freiburg.informatik.ultimate.lib.sifa.statistics.SifaStats.Key;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;

public final class InterferenceUtils {

	private InterferenceUtils() {
	}

	public static boolean modifiesGlobals(final TransFormula tf) {
		return tf.getAssignedVars().stream().anyMatch(IProgramVar::isGlobal);
	}

	public static String getForkedThreadOrNull(final IcfgEdge edge) {
		if (edge instanceof final IIcfgForkTransitionThreadCurrent<?> forkEdge) {
			return forkEdge.getNameOfForkedProcedure();
		}
		return null;
	}

	public static boolean isJoinAssigningGlobal(final IcfgEdge edge) {
		if (edge instanceof final IIcfgJoinTransitionThreadCurrent<?> joinCurrent) {
			return joinCurrent.getJoinSmtArguments().getAssignmentLhs().stream().anyMatch(IProgramVar::isGlobal);
		}
		if (edge instanceof final IIcfgJoinTransitionThreadOther<?> joinOther) {
			return modifiesGlobals(joinOther.getAssignmentOfJoin());
		}
		return false;
	}

	public static Set<IProgramVar> getJoinAssignedGlobals(final IcfgEdge edge) {
		if (!(edge instanceof final IIcfgJoinTransitionThreadCurrent<?> joinCurrent)) {
			return Set.of();
		}
		final List<IProgramVar> globals =
				joinCurrent.getJoinSmtArguments().getAssignmentLhs().stream().filter(IProgramVar::isGlobal).toList();
		return globals.isEmpty() ? Set.of() : Set.copyOf(globals);
	}

	static List<PreparedRelation> prepareNonFalseRelations(final Collection<IPredicate> relations,
			final RelationalPredicatePostcondition postcondition) {
		final List<PreparedRelation> prepared = new ArrayList<>();
		for (final IPredicate relation : relations) {
			if (!SmtUtils.isFalseLiteral(relation.getFormula())) {
				prepared.add(postcondition.prepareRelation(relation));
			}
		}
		return prepared;
	}

	static IPredicate applyUntilFixpoint(final IPredicate state, final List<PreparedRelation> preparedRelations,
			final IDomain domain, final RelationalPredicatePostcondition postcondition, final int wideningThreshold,
			final SifaStats stats) {
		// opt: nothing to apply
		if (preparedRelations.isEmpty() || SmtUtils.isTrueLiteral(state.getFormula())
				|| SmtUtils.isFalseLiteral(state.getFormula())) {
			return state;
		}

		IPredicate current = state;
		IPredicate frontier = state;
		for (int iteration = 1;; iteration++) {
			stats.increment(Key.INTERFERENCE_INNER_ITERATIONS);
			boolean hasGenerated = false;
			IPredicate generated = current;
			for (final PreparedRelation prepared : preparedRelations) {
				stats.increment(Key.INTERFERENCE_SP_APPLICATIONS);
				stats.start(Key.INTERFERENCE_SP_TIME);
				final IPredicate post = postcondition.strongestPostcondition(frontier, prepared);
				stats.stop(Key.INTERFERENCE_SP_TIME);
				// opt: false SP contributes nothing
				if (SmtUtils.isFalseLiteral(post.getFormula())) {
					continue;
				}
				if (!hasGenerated) {
					generated = post;
					hasGenerated = true;
				} else {
					generated = domain.join(generated, post);
				}
			}
			if (!hasGenerated || domain.isSubsetEq(generated, current).isTrueForAbstraction()) {
				return current;
			}

			final IPredicate expanded = domain.join(current, generated);
			final IPredicate next;
			if (iteration > wideningThreshold) {
				next = domain.widen(current, expanded);
				stats.increment(Key.INTERFERENCE_INNER_WIDENINGS);
			} else {
				next = expanded;
			}
			if (domain.isSubsetEq(next, current).isTrueForAbstraction()) {
				return current;
			}
			current = next;
			frontier = generated;
		}
	}

	static <K> Map<K, IPredicate> widenBuckets(final Map<K, IPredicate> left, final Map<K, IPredicate> right,
			final IDomain domain) {
		final Map<K, IPredicate> widened = new HashMap<>();
		for (final K key : left.keySet()) {
			final IPredicate thisPred = left.get(key);
			final IPredicate otherPred = right.get(key);
			widened.put(key, otherPred == null ? thisPred : domain.widen(thisPred, otherPred));
		}
		for (final K key : right.keySet()) {
			widened.putIfAbsent(key, right.get(key));
		}
		return widened;
	}

	static <K> Map<K, GuardedPredicate> widenGuardedBuckets(final Map<K, GuardedPredicate> left,
			final Map<K, GuardedPredicate> right, final IDomain domain) {
		final Map<K, GuardedPredicate> widened = new HashMap<>();
		for (final K key : left.keySet()) {
			final GuardedPredicate thisGp = left.get(key);
			final GuardedPredicate otherGp = right.get(key);
			if (otherGp == null) {
				widened.put(key, thisGp);
			} else {
				widened.put(key, widenGuardedPredicate(thisGp, otherGp, domain));
			}
		}
		for (final K key : right.keySet()) {
			widened.putIfAbsent(key, right.get(key));
		}
		return widened;
	}

	static GuardedPredicate widenGuardedPredicate(final GuardedPredicate left, final GuardedPredicate right,
			final IDomain domain) {
		final IPredicate widenedEffect = domain.widen(left.effect(), right.effect());
		final IPredicate widenedGuard;
		if (left.hasGuard() && right.hasGuard()) {
			widenedGuard = domain.widen(left.guard(), right.guard());
		} else {
			widenedGuard = null;
		}
		return new GuardedPredicate(widenedGuard, widenedEffect, mergeModifiedGlobals(left, right));
	}

	/** Merge modified globals sets: union if both present, null otherwise. */
	static Set<TermVariable> mergeModifiedGlobals(final GuardedPredicate left, final GuardedPredicate right) {
		if (!left.hasModifiedGlobals() || !right.hasModifiedGlobals()) {
			return null;
		}
		final Set<TermVariable> merged = new HashSet<>(left.modifiedGlobals());
		merged.addAll(right.modifiedGlobals());
		return Set.copyOf(merged);
	}
}
