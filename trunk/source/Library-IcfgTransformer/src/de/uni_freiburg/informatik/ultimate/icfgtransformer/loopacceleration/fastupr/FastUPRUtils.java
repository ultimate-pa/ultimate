package de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.fastupr;

import java.util.ArrayList;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.TransFormulaUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;

public class FastUPRUtils {

	private FastUPRUtils() {
		// Prevent instantiation of this utility class
	}

	public static UnmodifiableTransFormula composition(final ILogger logger, final IUltimateServiceProvider services,
			final ManagedScript managedScript, final UnmodifiableTransFormula formula, final int count) {
		final ArrayList<UnmodifiableTransFormula> formulas = new ArrayList<>();
		for (int i = 1; i <= count; i++) {
			formulas.add(formula);
		}

		return TransFormulaUtils.sequentialComposition(logger, services, managedScript, false, false, false,
				XnfConversionTechnique.BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION, SimplificationTechnique.SIMPLIFY_DDA,
				formulas);

	}
}
