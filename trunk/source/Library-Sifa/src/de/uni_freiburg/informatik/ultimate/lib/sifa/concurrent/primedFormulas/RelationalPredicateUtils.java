package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.primedFormulas;

import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.setup.ThreadModularSifaSettings.QuantifierEliminationMode;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.quantifier.PartialQuantifierElimination;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

public final class RelationalPredicateUtils {

	private RelationalPredicateUtils() {
	}

	public static Term existentiallyProject(final Term formula, final Set<TermVariable> varsToProject,
			final IUltimateServiceProvider services, final ManagedScript mgdScript) {
		return existentiallyProject(formula, varsToProject, services, mgdScript, QuantifierEliminationMode.LIGHT);
	}

	public static Term existentiallyProject(final Term formula, final Set<TermVariable> varsToProject,
			final IUltimateServiceProvider services, final ManagedScript mgdScript,
			final QuantifierEliminationMode eliminationMode) {
		if (varsToProject.isEmpty()) {
			return formula;
		}
		final Term quantified = SmtUtils.quantifier(mgdScript.getScript(), Script.EXISTS, varsToProject, formula);
		if (eliminationMode == QuantifierEliminationMode.STRONG) {
			return PartialQuantifierElimination.eliminate(services, mgdScript, quantified,
					SimplificationTechnique.SIMPLIFY_DDA2);
		}
		return PartialQuantifierElimination.eliminateLight(services, mgdScript, quantified);
	}
}
