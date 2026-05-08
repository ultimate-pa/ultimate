package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference;

import java.util.Comparator;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map.Entry;
import java.util.Objects;
import java.util.Set;
import java.util.function.Function;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgForkTransitionThreadCurrent;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgJoinTransitionThreadCurrent;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgJoinTransitionThreadOther;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.primedFormulas.RelationalPredicateUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

public final class InterferenceUtils {

	public static final Comparator<TranslatedInterferenceOfEdge> PREPARED_EDGE_ORDER =
			Comparator.comparing((TranslatedInterferenceOfEdge edge) -> edge.source().toString())
					.thenComparing(edge -> edge.target().toString())
					.thenComparing(edge -> edge.transitionPredicate().getFormula().toString());

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

	public static Set<TermVariable> getChangedGlobalTermVars(final TransFormula tf) {
		return getChangedGlobals(tf).stream().map(IProgramVar::getTermVariable)
				.collect(Collectors.toUnmodifiableSet());
	}

	public static Set<TermVariable> getChangedGlobalTermVars(final TransFormula tf,
			final Set<IProgramVar> additionallyChangedGlobals) {
		return getChangedGlobals(tf, additionallyChangedGlobals).stream().map(IProgramVar::getTermVariable)
				.collect(Collectors.toUnmodifiableSet());
	}

	public static boolean modifiesGlobals(final TransFormula tf) {
		return !getChangedGlobals(tf).isEmpty();
	}

	public static boolean writesAnyOf(final TransFormula tf, final Set<IProgramVar> vars) {
		return tf != null && !vars.isEmpty() && getChangedVars(tf).stream().anyMatch(vars::contains);
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

	public static boolean shouldSkipTrivialPredicate(final IPredicate predicate) {
		return predicate == null || SmtUtils.isTrueLiteral(predicate.getFormula()) || SmtUtils.isFalseLiteral(predicate.getFormula());
	}

	public static IPredicate projectToGlobalState(final IPredicate state, final IUltimateServiceProvider services,
			final ManagedScript script, final Function<Term, IPredicate> wrap) {
		return projectToGlobalState(state, Set.of(), services, script, wrap);
	}

	public static IPredicate projectToGlobalState(final IPredicate state, final Set<TermVariable> extraVarsToProject,
			final IUltimateServiceProvider services, final ManagedScript script, final Function<Term, IPredicate> wrap) {
		final Set<TermVariable> toProject = state.getVars().stream().filter(v -> !v.isGlobal())
				.map(IProgramVar::getTermVariable).collect(Collectors.toCollection(HashSet::new));
		toProject.addAll(extraVarsToProject);
		if (toProject.isEmpty()) {
			return state;
		}
		return wrap.apply(RelationalPredicateUtils.existentiallyProject(state.getFormula(), toProject, services, script));
	}

	private static Set<IProgramVar> filterGlobals(final Set<IProgramVar> variables) {
		return variables.stream().filter(IProgramVar::isGlobal).collect(Collectors.toCollection(LinkedHashSet::new));
	}
}
