package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.primedFormulas;

import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.quantifier.PartialQuantifierElimination;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.quantifier.QuantifierUtils;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

public final class RelationalPredicateUtils {

	private RelationalPredicateUtils() {
	}

	public static Term existentiallyProject(final Term formula, final Set<TermVariable> varsToProject,
			final IUltimateServiceProvider services, final ManagedScript mgdScript) {
		if (varsToProject.isEmpty()) {
			return formula;
		}
		final Term quantified = SmtUtils.quantifier(mgdScript.getScript(), Script.EXISTS, varsToProject, formula);
		final Term lightResult = PartialQuantifierElimination.eliminateLight(services, mgdScript, quantified);
		if (QuantifierUtils.isQuantifierFree(lightResult)) {
			return lightResult;
		}
		// light QE didn't eliminate all quantifiers, fall back to full elimination
		return PartialQuantifierElimination.eliminate(services, mgdScript, quantified,
				SimplificationTechnique.SIMPLIFY_DDA2);
	}
}