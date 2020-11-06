package de.uni_freiburg.informatik.ultimate.lib.mcr;

import java.util.Arrays;
import java.util.Collection;
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.PartialQuantifierElimination;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

public class McrUtils {
	private McrUtils() {
	}

	public static Set<TermVariable> getTermVariables(final Collection<IProgramVar> vars) {
		return vars.stream().map(IProgramVar::getTermVariable).collect(Collectors.toSet());
	}

	public static Term abstractVariables(final Term term, final Set<TermVariable> varsToKeep, final int quantifier,
			final ManagedScript managedScript, final IUltimateServiceProvider services,
			final ILogger logger, final SimplificationTechnique simplificationTechnique,
			final XnfConversionTechnique xnfConversionTechnique) {
		final Term eliminated = PartialQuantifierElimination.tryToEliminate(services, logger, managedScript, term,
				simplificationTechnique, xnfConversionTechnique);
		final Term normalForm;
		switch (quantifier) {
		case QuantifiedFormula.EXISTS:
			normalForm = SmtUtils.toDnf(services, managedScript, eliminated, xnfConversionTechnique);
			break;
		case QuantifiedFormula.FORALL:
			normalForm = SmtUtils.toCnf(services, managedScript, eliminated, xnfConversionTechnique);
			break;
		default:
			throw new AssertionError("Invalid Qunatifier!");
		}
		final List<TermVariable> quantifiedVars = Arrays.stream(normalForm.getFreeVars())
				.filter(x -> !varsToKeep.contains(x)).collect(Collectors.toList());
		final Term quantified = SmtUtils.quantifier(managedScript.getScript(), quantifier, quantifiedVars, normalForm);
		return PartialQuantifierElimination.tryToEliminate(services, logger, managedScript, quantified,
				simplificationTechnique, xnfConversionTechnique);
	}
}
