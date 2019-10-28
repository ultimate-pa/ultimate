package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.independencerelation;

import java.util.Arrays;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.ModelCheckerUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaBuilder;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;

/**
 * An independence relation that implements an SMT-based inclusion or equality
 * check on the semantics.
 *
 * It is recommended to wrap this relation in a
 * {@link CachedIndependenceRelation} for better performance.
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 */

public class SemanticIndependenceRelation implements IIndependenceRelation<IPredicate, IIcfgTransition<?>> {

	private final IUltimateServiceProvider mServices;
	private final ManagedScript mManagedScript;
	private final ILogger mLogger;

	private final static SimplificationTechnique mSimplificationTechnique = SimplificationTechnique.SIMPLIFY_DDA;
	private final static XnfConversionTechnique mXnfConversionTechnique = XnfConversionTechnique.BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION;

	private final boolean mConditional;
	private final boolean mSymmetric;

	/**
	 * Create a new variant of the semantic independence relation.
	 *
	 * @param conditional
	 *            If set to true, the relation will be conditional: It will use the
	 *            given {@link IPredicate} as context to enable additional
	 *            commutativity. This subsumes the non-conditional variant.
	 * @param symmetric
	 *            If set to true, the relation will check for full commutativity. If
	 *            false, only semicommutativity is checked, which subsumes full
	 *            commutativity.
	 */
	public SemanticIndependenceRelation(final IUltimateServiceProvider services, final ManagedScript mgdScript,
			final boolean conditional, final boolean symmetric) {
		mServices = services;
		mManagedScript = mgdScript;
		mLogger = services.getLoggingService().getLogger(ModelCheckerUtils.PLUGIN_ID);

		mConditional = conditional;
		mSymmetric = symmetric;
	}

	@Override
	public boolean isSymmetric() {
		return mSymmetric;
	}

	@Override
	public boolean isConditional() {
		return mConditional;
	}

	@Override
	public boolean contains(final IPredicate state, final IIcfgTransition<?> a, final IIcfgTransition<?> b) {
		final IPredicate context = mConditional ? state : null;
		final boolean subset = performInclusionCheck(context, a, b);

		if (mSymmetric) {
			final boolean superset = performInclusionCheck(context, b, a);
			return subset && superset;
		} else {
			return subset;
		}
	}

	private final boolean performInclusionCheck(final IPredicate context, final IIcfgTransition<?> a,
			final IIcfgTransition<?> b) {
		final UnmodifiableTransFormula transFormula1 = compose(a.getTransformula(), b.getTransformula());
		UnmodifiableTransFormula transFormula2 = compose(b.getTransformula(), a.getTransformula());

		if (context != null) {
			// TODO: This represents conjunction with guard (precondition) as composition
			// with assume. Is this a good way?
			final UnmodifiableTransFormula guard = TransFormulaBuilder.constructTransFormulaFromPredicate(context,
					mManagedScript);
			transFormula2 = compose(guard, transFormula2);
		}

		final LBool result = TransFormulaUtils.checkImplication(transFormula2, transFormula1, mManagedScript);
		return result == LBool.UNSAT;
	}

	private final UnmodifiableTransFormula compose(final UnmodifiableTransFormula first,
			final UnmodifiableTransFormula second) {
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
