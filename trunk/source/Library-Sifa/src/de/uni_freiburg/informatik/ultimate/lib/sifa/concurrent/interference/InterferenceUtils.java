package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgForkTransitionThreadCurrent;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgJoinTransitionThreadCurrent;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgJoinTransitionThreadOther;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.BasicPredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.primedFormulas.RelationalPredicatePostcondition;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.primedFormulas.RelationalPredicatePostcondition.PreparedRelation;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.primedFormulas.RelationalPredicateUtils;
import de.uni_freiburg.informatik.ultimate.lib.sifa.domain.IDomain;
import de.uni_freiburg.informatik.ultimate.lib.sifa.statistics.SifaStats;
import de.uni_freiburg.informatik.ultimate.lib.sifa.statistics.SifaStats.Key;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.Substitution;

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
				final IPredicate post = perDisjunctSP(frontier, prepared, postcondition, stats);
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

	/**
	 * Per-disjunct strongest postcondition: splits the state into top-level disjuncts and applies the relational
	 * predicate to each independently. This avoids QE on large disjunctive formulas.
	 * Pre-vars are projected using equality substitution where possible, falling back to QE for the rest.
	 */
	static IPredicate perDisjunctSP(final IPredicate statePredicate, final PreparedRelation prepared,
			final RelationalPredicatePostcondition postcondition, final SifaStats stats) {
		final ManagedScript managedScript = postcondition.getManagedScript();
		final BasicPredicateFactory predicateFactory = postcondition.getPredicateFactory();
		final IUltimateServiceProvider services = postcondition.getServices();

		final Term stateFormula = statePredicate.getFormula();
		if (SmtUtils.isFalseLiteral(stateFormula) || SmtUtils.isFalseLiteral(prepared.relation().getFormula())) {
			return predicateFactory.newPredicate(managedScript.getScript().term("false"));
		}

		final Term[] disjuncts = getTopLevelDisjuncts(stateFormula);
		final Script script = managedScript.getScript();
		final Term relationFormula = prepared.relation().getFormula();
		final Set<TermVariable> preVarsToProject = prepared.preVarsToProject();
		final Map<Term, Term> primedToUnprimed = prepared.primedToUnprimed();

		final List<Term> resultTerms = new ArrayList<>();
		for (final Term disjunct : disjuncts) {
			final Term conjunction = SmtUtils.andWithExtendedLocalSimplification(script, disjunct, relationFormula);
			if (SmtUtils.isFalseLiteral(conjunction)) {
				continue;
			}

			final Term projected;
			if (preVarsToProject.isEmpty() || !hasFreeVarIn(conjunction, preVarsToProject)) {
				projected = conjunction;
			} else {
				projected = projectPreVarsWithSubstitution(conjunction, preVarsToProject, script, services,
						managedScript, stats);
			}

			final Term renamed;
			if (primedToUnprimed.isEmpty() || !hasFreeVarIn(projected, primedToUnprimed.keySet())) {
				renamed = projected;
			} else {
				renamed = Substitution.apply(managedScript, primedToUnprimed, projected);
			}

			if (!SmtUtils.isFalseLiteral(renamed)) {
				resultTerms.add(renamed);
			}
		}

		if (resultTerms.isEmpty()) {
			return predicateFactory.newPredicate(script.term("false"));
		}
		if (resultTerms.size() == 1) {
			return predicateFactory.newPredicate(resultTerms.get(0));
		}
		return predicateFactory.newPredicate(SmtUtils.or(script, resultTerms.toArray(new Term[resultTerms.size()])));
	}

	/** Substitute equalities for projected vars; fall back to QE for any that remain. */
	private static Term projectPreVarsWithSubstitution(final Term conjunction, final Set<TermVariable> toProject,
			final Script script, final IUltimateServiceProvider services, final ManagedScript managedScript,
			final SifaStats stats) {
		final Term[] conjuncts = getTopLevelConjuncts(conjunction);

		final Map<Term, Term> substitution = new HashMap<>();
		for (final Term conjunct : conjuncts) {
			final TermVariable solved = solveEqualityForProjected(conjunct, toProject);
			if (solved != null && !substitution.containsKey(solved)) {
				final Term value = getEqualityOtherSide(conjunct, solved);
				if (value != null && Collections.disjoint(Arrays.asList(value.getFreeVars()), toProject)) {
					substitution.put(solved, value);
				}
			}
		}

		Term[] workingConjuncts = conjuncts;
		if (!substitution.isEmpty()) {
			workingConjuncts = new Term[conjuncts.length];
			for (int i = 0; i < conjuncts.length; i++) {
				workingConjuncts[i] = Substitution.apply(managedScript, substitution, conjuncts[i]);
			}
		}

		final Set<TermVariable> remaining = new HashSet<>();
		final List<Term> kept = new ArrayList<>();
		for (final Term conjunct : workingConjuncts) {
			boolean mentionsProjected = false;
			for (final TermVariable fv : conjunct.getFreeVars()) {
				if (toProject.contains(fv)) {
					mentionsProjected = true;
					remaining.add(fv);
				}
			}
			if (!mentionsProjected) {
				kept.add(conjunct);
			}
		}

		if (remaining.isEmpty()) {
			stats.increment(Key.INTERFERENCE_QE_LIGHT);
			if (kept.size() == workingConjuncts.length && substitution.isEmpty()) {
				return conjunction;
			}
			if (kept.isEmpty()) {
				return script.term("true");
			}
			if (kept.size() == 1) {
				return kept.get(0);
			}
			return SmtUtils.and(script, kept.toArray(new Term[kept.size()]));
		}

		final Term reduced;
		if (substitution.isEmpty()) {
			reduced = conjunction;
		} else {
			reduced = SmtUtils.and(script, workingConjuncts);
		}
		return RelationalPredicateUtils.existentiallyProject(reduced, remaining, services, managedScript, stats);
	}

	private static TermVariable solveEqualityForProjected(final Term term, final Set<TermVariable> toProject) {
		if (!(term instanceof final ApplicationTerm app) || !"=".equals(app.getFunction().getName())
				|| app.getParameters().length != 2) {
			return null;
		}
		final Term lhs = app.getParameters()[0];
		final Term rhs = app.getParameters()[1];
		if (lhs instanceof final TermVariable lv && toProject.contains(lv)) {
			return lv;
		}
		if (rhs instanceof final TermVariable rv && toProject.contains(rv)) {
			return rv;
		}
		return null;
	}

	private static Term getEqualityOtherSide(final Term equality, final TermVariable var) {
		final ApplicationTerm app = (ApplicationTerm) equality;
		final Term lhs = app.getParameters()[0];
		final Term rhs = app.getParameters()[1];
		if (lhs == var) {
			return rhs;
		}
		if (rhs == var) {
			return lhs;
		}
		return null;
	}

	private static Term[] getTopLevelDisjuncts(final Term formula) {
		if (formula instanceof final ApplicationTerm app && "or".equals(app.getFunction().getName())) {
			return app.getParameters();
		}
		return new Term[] { formula };
	}

	private static Term[] getTopLevelConjuncts(final Term formula) {
		if (formula instanceof final ApplicationTerm app && "and".equals(app.getFunction().getName())) {
			return app.getParameters();
		}
		return new Term[] { formula };
	}

	static boolean hasFreeVarIn(final Term term, final Set<? extends Term> candidates) {
		for (final TermVariable freeVar : term.getFreeVars()) {
			if (candidates.contains(freeVar)) {
				return true;
			}
		}
		return false;
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
