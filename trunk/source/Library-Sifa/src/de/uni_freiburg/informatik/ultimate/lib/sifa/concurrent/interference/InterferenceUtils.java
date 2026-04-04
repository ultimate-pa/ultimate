package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Objects;
import java.util.Set;

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
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.factories.PredicateWithSrcAndTrgt;
import de.uni_freiburg.informatik.ultimate.lib.sifa.statistics.SifaStats;
import de.uni_freiburg.informatik.ultimate.lib.sifa.statistics.SifaStats.Key;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

public final class InterferenceUtils {

	public static final Comparator<PredicateWithSrcAndTrgt> EDGE_PREDICATE_ORDER =
			Comparator.comparing((PredicateWithSrcAndTrgt p) -> p.source().toString())
					.thenComparing(p -> p.target().toString())
					.thenComparing(p -> p.predicate().getFormula().toString());

	@FunctionalInterface
	public interface GuardedTransformer {
		IPredicate apply(IPredicate frontier, GuardedPredicate predicate);
	}

	private InterferenceUtils() {
	}

	public static Set<IProgramVar> getChangedVars(final TransFormula tf) {
		if (tf == null) {
			return Set.of();
		}
		final Set<IProgramVar> changed = new LinkedHashSet<>(tf.getAssignedVars());
		for (final Entry<IProgramVar, TermVariable> entry : tf.getOutVars().entrySet()) {
			final IProgramVar variable = entry.getKey();
			final TermVariable outVar = entry.getValue();
			final TermVariable inVar = tf.getInVars().get(variable);
			if (!Objects.equals(outVar, inVar)) {
				changed.add(variable);
			}
		}
		return changed.isEmpty() ? Set.of() : Set.copyOf(changed);
	}

	public static Set<IProgramVar> getChangedGlobals(final TransFormula tf) {
		return filterGlobals(getChangedVars(tf));
	}

	public static Set<IProgramVar> getChangedGlobals(final TransFormula tf,
			final Set<IProgramVar> additionallyChangedGlobals) {
		final Set<IProgramVar> changedGlobals = new LinkedHashSet<>(getChangedGlobals(tf));
		if (additionallyChangedGlobals != null) {
			for (final IProgramVar variable : additionallyChangedGlobals) {
				if (variable.isGlobal()) {
					changedGlobals.add(variable);
				}
			}
		}
		return changedGlobals.isEmpty() ? Set.of() : Set.copyOf(changedGlobals);
	}

	public static Set<TermVariable> getChangedGlobalTermVars(final TransFormula tf,
			final Set<IProgramVar> additionallyChangedGlobals) {
		final Set<TermVariable> changedTerms = new LinkedHashSet<>();
		for (final IProgramVar variable : getChangedGlobals(tf, additionallyChangedGlobals)) {
			changedTerms.add(variable.getTermVariable());
		}
		return changedTerms.isEmpty() ? Set.of() : Set.copyOf(changedTerms);
	}

	public static boolean modifiesGlobals(final TransFormula tf) {
		return !getChangedGlobals(tf).isEmpty();
	}

	public static boolean writesAnyOf(final TransFormula tf, final Set<IProgramVar> vars) {
		if (tf == null || vars.isEmpty()) {
			return false;
		}
		for (final IProgramVar variable : getChangedVars(tf)) {
			if (vars.contains(variable)) {
				return true;
			}
		}
		return false;
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

	public static Set<IProgramVar> getAdditionalChangedGlobals(final IcfgEdge edge) {
		if (!(edge instanceof final IIcfgJoinTransitionThreadCurrent<?> joinCurrent)) {
			return Set.of();
		}
		final List<IProgramVar> globals =
				joinCurrent.getJoinSmtArguments().getAssignmentLhs().stream().filter(IProgramVar::isGlobal).toList();
		return globals.isEmpty() ? Set.of() : Set.copyOf(globals);
	}

	public static boolean hasRelevantInterferenceEffect(final IcfgEdge edge) {
		if (edge == null) {
			return false;
		}
		return getForkedThreadOrNull(edge) != null || isJoinAssigningGlobal(edge) || modifiesGlobals(edge.getTransformula());
	}

	public static List<PreparedRelation> prepareNonFalseRelations(final Collection<IPredicate> relations,
			final RelationalPredicatePostcondition postcondition) {
		final List<PreparedRelation> prepared = new ArrayList<>();
		for (final IPredicate relation : relations) {
			if (!SmtUtils.isFalseLiteral(relation.getFormula())) {
				prepared.add(postcondition.prepareRelation(relation));
			}
		}
		return prepared;
	}

	public static IPredicate applyUntilFixpoint(final IPredicate state, final List<PreparedRelation> preparedRelations,
			final IDomain domain, final RelationalPredicatePostcondition postcondition, final int wideningThreshold,
			final SifaStats stats) {
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

	public static IPredicate applyUntilFixpoint(final IPredicate state, final Collection<GuardedPredicate> predicates,
			final IDomain domain, final int wideningThreshold, final SifaStats stats,
			final GuardedTransformer transformer) {
		if (predicates.isEmpty() || SmtUtils.isTrueLiteral(state.getFormula())
				|| SmtUtils.isFalseLiteral(state.getFormula())) {
			return state;
		}

		IPredicate current = state;
		IPredicate frontier = state;
		for (int iteration = 1;; iteration++) {
			stats.increment(Key.INTERFERENCE_INNER_ITERATIONS);
			boolean hasGenerated = false;
			IPredicate generated = current;
			for (final GuardedPredicate predicate : predicates) {
				final IPredicate post = transformer.apply(frontier, predicate);
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

	public static <K> Map<K, GuardedPredicate> widenGuardedBuckets(final Map<K, GuardedPredicate> left,
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

	static Set<TermVariable> mergeModifiedGlobals(final GuardedPredicate left, final GuardedPredicate right) {
		if (!left.hasModifiedGlobals() || !right.hasModifiedGlobals()) {
			return null;
		}
		final Set<TermVariable> merged = new HashSet<>(left.modifiedGlobals());
		merged.addAll(right.modifiedGlobals());
		return Set.copyOf(merged);
	}

	public static void collectConjuncts(final Term formula, final List<Term> result) {
		final Term[] conjuncts = SmtUtils.getConjuncts(formula);
		if (conjuncts.length == 1 && conjuncts[0] == formula) {
			result.add(formula);
		} else {
			for (final Term param : conjuncts) {
				collectConjuncts(param, result);
			}
		}
	}

	private static Set<IProgramVar> filterGlobals(final Set<IProgramVar> variables) {
		if (variables.isEmpty()) {
			return Set.of();
		}
		final Set<IProgramVar> globals = new LinkedHashSet<>();
		for (final IProgramVar variable : variables) {
			if (variable.isGlobal()) {
				globals.add(variable);
			}
		}
		return globals.isEmpty() ? Set.of() : Set.copyOf(globals);
	}
}
