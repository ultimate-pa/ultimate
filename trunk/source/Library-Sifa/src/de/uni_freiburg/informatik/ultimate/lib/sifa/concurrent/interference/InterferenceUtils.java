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
import de.uni_freiburg.informatik.ultimate.lib.sifa.statistics.SifaStats;
import de.uni_freiburg.informatik.ultimate.lib.sifa.statistics.SifaStats.Key;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

public final class InterferenceUtils {

	static final Comparator<PredicateWithSrcAndTrgt> EDGE_PREDICATE_ORDER =
			Comparator.comparing((PredicateWithSrcAndTrgt p) -> p.source().toString())
					.thenComparing(p -> p.target().toString())
					.thenComparing(p -> p.predicate().getFormula().toString());

	@FunctionalInterface
	interface GuardedTransformer {
		IPredicate apply(IPredicate frontier, GuardedPredicate predicate);
	}

	private InterferenceUtils() {
	}

	/** Over-approximation of the write set: assigned vars + vars with distinct out-variable. */
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

	static IPredicate applyUntilFixpoint(final IPredicate state, final Collection<GuardedPredicate> predicates,
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

	static Set<TermVariable> mergeModifiedGlobals(final GuardedPredicate left, final GuardedPredicate right) {
		if (!left.hasModifiedGlobals() || !right.hasModifiedGlobals()) {
			return null;
		}
		final Set<TermVariable> merged = new HashSet<>(left.modifiedGlobals());
		merged.addAll(right.modifiedGlobals());
		return Set.copyOf(merged);
	}

	public static Term[] getTopLevelDisjuncts(final Term formula) {
		if (formula instanceof final ApplicationTerm app && "or".equals(app.getFunction().getName())) {
			return app.getParameters();
		}
		return new Term[] { formula };
	}

	static void collectConjuncts(final Term formula, final List<Term> result) {
		if (formula instanceof final ApplicationTerm app && "and".equals(app.getFunction().getName())) {
			for (final Term param : app.getParameters()) {
				collectConjuncts(param, result);
			}
		} else {
			result.add(formula);
		}
	}

	static boolean areSyntacticallyContradictory(final Term left, final Term right) {
		final List<Term> conjuncts = new ArrayList<>();
		collectConjuncts(left, conjuncts);
		collectConjuncts(right, conjuncts);
		return hasEqualityContradiction(conjuncts);
	}

	static boolean hasEqualityContradiction(final List<Term> conjuncts) {
		final Map<TermVariable, Set<Term>> possibleValues = new HashMap<>();
		for (final Term conjunct : conjuncts) {
			TermVariable var = null;
			Set<Term> values = null;
			if (conjunct instanceof final ApplicationTerm app) {
				if ("=".equals(app.getFunction().getName()) && app.getParameters().length == 2) {
					final Term lhs = app.getParameters()[0];
					final Term rhs = app.getParameters()[1];
					if (lhs instanceof final TermVariable tv && rhs.getFreeVars().length == 0) {
						var = tv;
						values = Set.of(rhs);
					} else if (rhs instanceof final TermVariable tv && lhs.getFreeVars().length == 0) {
						var = tv;
						values = Set.of(lhs);
					}
				} else if ("or".equals(app.getFunction().getName())) {
					final var extracted = extractDisjunctiveEquality(app);
					if (extracted != null) {
						var = extracted.getKey();
						values = extracted.getValue();
					}
				}
			}
			if (var == null) {
				continue;
			}
			final Set<Term> existing = possibleValues.get(var);
			if (existing == null) {
				possibleValues.put(var, new HashSet<>(values));
			} else {
				existing.retainAll(values);
				if (existing.isEmpty()) {
					return true;
				}
			}
		}
		return false;
	}

	private static Map.Entry<TermVariable, Set<Term>> extractDisjunctiveEquality(final ApplicationTerm or) {
		TermVariable var = null;
		final Set<Term> values = new HashSet<>();
		for (final Term disjunct : or.getParameters()) {
			if (!(disjunct instanceof final ApplicationTerm eq) || !"=".equals(eq.getFunction().getName())
					|| eq.getParameters().length != 2) {
				return null;
			}
			final Term lhs = eq.getParameters()[0];
			final Term rhs = eq.getParameters()[1];
			TermVariable tv;
			Term val;
			if (lhs instanceof TermVariable && rhs.getFreeVars().length == 0) {
				tv = (TermVariable) lhs;
				val = rhs;
			} else if (rhs instanceof TermVariable && lhs.getFreeVars().length == 0) {
				tv = (TermVariable) rhs;
				val = lhs;
			} else {
				return null;
			}
			if (var == null) {
				var = tv;
			} else if (!var.equals(tv)) {
				return null;
			}
			values.add(val);
		}
		return var == null ? null : Map.entry(var, values);
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
