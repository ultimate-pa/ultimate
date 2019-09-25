package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstractionconcurrent.reduction;

import java.util.Arrays;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.Activator;

/**
 * An independence relation that implements an SMT-based inclusion check on the semantics.
 * 
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 *
 * @param <STATE> This relation is non-conditional, so this parameter is not used.
 */

public class SemanticIndependenceRelation<STATE> implements IIndependenceRelation<STATE, IIcfgTransition<?>> {

	private final IUltimateServiceProvider mServices;
	private final ManagedScript mManagedScript;
	private final ILogger mLogger;

	private final SimplificationTechnique mSimplificationTechnique = SimplificationTechnique.SIMPLIFY_DDA;
	private final XnfConversionTechnique mXnfConversionTechnique = XnfConversionTechnique.BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION;

	public SemanticIndependenceRelation(final IUltimateServiceProvider services, final ManagedScript mgdScript) {
		mServices = services;
		mManagedScript = mgdScript;
		mLogger = services.getLoggingService().getLogger(Activator.PLUGIN_ID);
	}

	@Override
	public boolean isSymmetric() {
		return false;
	}

	@Override
	public boolean isConditional() {
		return false;
	}

	@Override
	public boolean contains(final STATE state, final IIcfgTransition<?> a, final IIcfgTransition<?> b) {
		final UnmodifiableTransFormula transFormula1 = compose(a.getTransformula(), b.getTransformula());
		final UnmodifiableTransFormula transFormula2 = compose(b.getTransformula(), a.getTransformula());
		final LBool result = TransFormulaUtils.checkImplication(transFormula2, transFormula1, mManagedScript);

		return result == LBool.UNSAT;
	}

	private final UnmodifiableTransFormula compose(final UnmodifiableTransFormula first, final UnmodifiableTransFormula second) {
		// no need to do simplification, result is only used in one implication check
		final boolean simplify = false;

		// try to eliminate auxiliary variables to avoid quantifier alternation in
		// implication check
		final boolean tryAuxVarElimination = true;

		return TransFormulaUtils.sequentialComposition(mLogger, mServices, mManagedScript, simplify,
				tryAuxVarElimination, false, mXnfConversionTechnique, mSimplificationTechnique,
				Arrays.asList(first, second));
	}
}
