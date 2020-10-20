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
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

public class McrUtils {
	private McrUtils() {
	}

	public static Set<TermVariable> getTermVariables(final Collection<IProgramVar> vars) {
		return vars.stream().map(IProgramVar::getTermVariable).collect(Collectors.toSet());
	}

	public static Term abstractVariables(final Term term, final Set<TermVariable> varsToKeep, final int quantifier,
			final IUltimateServiceProvider services, final ILogger logger, final ManagedScript managedScript,
			final SimplificationTechnique simplificationTechnique,
			final XnfConversionTechnique xnfConversionTechnique) {
		final List<TermVariable> quantifiedVars =
				Arrays.stream(term.getFreeVars()).filter(x -> !varsToKeep.contains(x)).collect(Collectors.toList());
		final Term quantified = SmtUtils.quantifier(managedScript.getScript(), quantifier, quantifiedVars, term);
		return PartialQuantifierElimination.tryToEliminate(services, logger, managedScript, quantified,
				simplificationTechnique, xnfConversionTechnique);
	}
}
