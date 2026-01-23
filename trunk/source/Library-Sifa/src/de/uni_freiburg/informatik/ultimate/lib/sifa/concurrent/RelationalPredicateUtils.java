package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent;

import java.util.ArrayList;
import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.quantifier.PartialQuantifierElimination;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

/**
 * Static utilities for working with relational predicates that use primed/unprimed variable conventions.
 */
public final class RelationalPredicateUtils {

	private RelationalPredicateUtils() {
		// utility class
	}

	/**
	 * Builds identity constraints (x = x') for unchanged variables.
	 *
	 * @param unchangedVars
	 *            variables that are unchanged (need x = x' constraint)
	 * @param symbolTable
	 *            provides primed variable mappings
	 * @param script
	 *            SMT script
	 * @return list of equality terms
	 */
	public static List<Term> buildIdentityConstraints(final Iterable<IProgramVar> unchangedVars,
			final PrimedDefaultIcfgSymbolTable symbolTable, final Script script) {
		final List<Term> equalities = new ArrayList<>();
		for (final IProgramVar pv : unchangedVars) {
			equalities.add(SmtUtils.binaryEquality(script, pv.getTermVariable(), symbolTable.getPrimedVar(pv)));
		}
		return equalities;
	}

	/**
	 * Conjoins a formula with identity constraints, or returns the formula unchanged if no constraints.
	 */
	public static Term conjoinWithIdentities(final Term formula, final List<Term> identities, final Script script) {
		if (identities.isEmpty()) {
			return formula;
		}
		identities.add(formula);
		return SmtUtils.and(script, identities);
	}

	/**
	 * Existentially projects away the given variables from the formula using quantifier elimination.
	 *
	 * @param useLightElimination
	 *            if true, uses lightweight elimination (faster but may leave quantifiers); if false, uses full
	 *            elimination
	 */
	public static Term existentiallyProject(final Term formula, final Set<TermVariable> varsToProject,
			final IUltimateServiceProvider services, final ManagedScript mgdScript, final boolean useLightElimination) {
		if (varsToProject.isEmpty()) {
			return formula;
		}
		final Term quantified = SmtUtils.quantifier(mgdScript.getScript(), Script.EXISTS, varsToProject, formula);
		if (useLightElimination) {
			return PartialQuantifierElimination.eliminateLight(services, mgdScript, quantified);
		}
		return PartialQuantifierElimination.eliminate(services, mgdScript, quantified,
				SimplificationTechnique.SIMPLIFY_DDA);
	}
}
