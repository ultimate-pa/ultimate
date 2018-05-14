package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.rcfg;

import java.util.function.Supplier;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.absint.DisjunctiveAbstractState;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.absint.IAbstractState;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.IIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.ICallAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgReturnTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IInternalAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IReturnAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hoaretriple.IHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hoaretriple.IHoareTripleChecker.Validity;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hoaretriple.IncrementalHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.AbsIntPredicate;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.BasicPredicate;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.TermVarsProc;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.IDebugHelper;

/**
 * Default implementation of {@link IDebugHelper}.
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 * @param <STATE>
 * @param <LOCATION>
 */
public class RcfgDebugHelper<STATE extends IAbstractState<STATE>, ACTION extends IAction, VARDECL, LOCATION>
		implements IDebugHelper<STATE, ACTION, VARDECL, LOCATION> {

	private static final boolean SIMPLIFY_IF_ASSERTION_FAILS = false;

	private final ILogger mLogger;
	private final IUltimateServiceProvider mServices;
	private final IHoareTripleChecker mHTC;
	private final ManagedScript mMgdScript;
	private final IIcfgSymbolTable mSymbolTable;

	private static int sIllegalPredicates = Integer.MAX_VALUE;

	public RcfgDebugHelper(final CfgSmtToolkit csToolkit, final IUltimateServiceProvider services,
			final IIcfgSymbolTable symbolTable) {
		mServices = services;
		mSymbolTable = symbolTable;
		mMgdScript = csToolkit.getManagedScript();
		mLogger = services.getLoggingService().getLogger(Activator.PLUGIN_ID);
		mHTC = new IncrementalHoareTripleChecker(csToolkit, false);
	}

	@Override
	public boolean isPostSound(final DisjunctiveAbstractState<STATE> preState,
			final DisjunctiveAbstractState<STATE> hierPreState, final DisjunctiveAbstractState<STATE> postState,
			final ACTION transition) {
		final IPredicate pre = createPredicateFromState(preState);
		final IPredicate post = createPredicateFromState(postState);
		final IPredicate hierPre = getHierachicalPre(transition, () -> createPredicateFromState(hierPreState));
		return isPostSound(hierPre, transition, pre, post);
	}

	private IPredicate getHierachicalPre(final ACTION transition, final Supplier<IPredicate> func) {
		if (transition instanceof IIcfgReturnTransition<?, ?>) {
			return func.get();
		}
		return null;
	}

	private boolean isPostSound(final IPredicate precondHier, final ACTION transition, final IPredicate precond,
			final IPredicate postcond) {
		try {
			final Validity result;
			if (transition instanceof ICallAction) {
				result = mHTC.checkCall(precond, (ICallAction) transition, postcond);
			} else if (transition instanceof IReturnAction) {
				result = mHTC.checkReturn(precond, precondHier, (IReturnAction) transition, postcond);
			} else {
				result = mHTC.checkInternal(precond, (IInternalAction) transition, postcond);
			}

			if (result != Validity.VALID) {
				logUnsoundness(transition, precond, postcond, precondHier);
			}
			return result != Validity.INVALID;
		} finally {
			mHTC.releaseLock();
		}
	}

	private void logUnsoundness(final ACTION transition, final IPredicate precond, final IPredicate postcond,
			final IPredicate precondHier) {
		mLogger.fatal("Soundness check failed for the following triple:");

		if (precondHier == null) {
			mLogger.fatal("Pre: {" + precond + "}");
		} else {
			mLogger.fatal("Pre: {" + precond + "}");
			mLogger.fatal("PreHier: {" + precondHier + "}");
		}
		mLogger.fatal(getTransformulaDebugString(transition) + " (" + transition + ")");
		mLogger.fatal("Post: {" + postcond + "}");

		if (SIMPLIFY_IF_ASSERTION_FAILS) {
			mLogger.fatal("Simplified triple ");
			final Term simplifiedPrecond = SmtUtils.simplify(mMgdScript, precond.getFormula(), mServices,
					SimplificationTechnique.SIMPLIFY_DDA);
			if (precondHier == null) {
				mLogger.fatal("Pre: {" + simplifiedPrecond + "}");
			} else {
				mLogger.fatal("Pre: {" + simplifiedPrecond + "}");
				mLogger.fatal("PreHier: {" + SmtUtils.simplify(mMgdScript, precondHier.getFormula(), mServices,
						SimplificationTechnique.SIMPLIFY_DDA) + "}");
			}
			mLogger.fatal(getTransformulaDebugString(transition) + " (" + transition + ")");
			mLogger.fatal("Post: {" + SmtUtils.simplify(mMgdScript, postcond.getFormula(), mServices,
					SimplificationTechnique.SIMPLIFY_DDA) + "}");
		}
	}

	private String getTransformulaDebugString(final ACTION action) {
		if (action instanceof IInternalAction) {
			return ((IInternalAction) action).getTransformula().getFormula().toStringDirect();
		} else if (action instanceof ICallAction) {
			return ((ICallAction) action).getLocalVarsAssignment().getFormula().toStringDirect();
		} else if (action instanceof IReturnAction) {
			return ((IReturnAction) action).getAssignmentOfReturn().getFormula().toStringDirect();
		} else {
			throw new UnsupportedOperationException("Cannot find transformula in " + action);
		}
	}

	private IPredicate createPredicateFromState(final DisjunctiveAbstractState<STATE> state) {
		final Term acc = state.getTerm(mMgdScript.getScript());
		final TermVarsProc tvp = TermVarsProc.computeTermVarsProc(acc, mMgdScript.getScript(), mSymbolTable);
		return new AbsIntPredicate<>(new BasicPredicate(getIllegalPredicateId(), tvp.getProcedures(), acc,
				tvp.getVars(), tvp.getClosedFormula()), state);
	}

	private static int getIllegalPredicateId() {
		return sIllegalPredicates--;
	}
}
