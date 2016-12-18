package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.rcfg;

import java.util.Collection;
import java.util.Set;
import java.util.function.Supplier;

import de.uni_freiburg.informatik.ultimate.abstractinterpretation.model.IAbstractState;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Util;
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
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.BasicPredicate;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.TermVarsProc;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.AbstractMultiState;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.IDebugHelper;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;

/**
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 * @param <STATE>
 * @param <LOCATION>
 */
public class RcfgDebugHelper<STATE extends IAbstractState<STATE, ACTION, VARDECL>, ACTION extends IAction, VARDECL, LOCATION>
		implements IDebugHelper<STATE, ACTION, VARDECL, LOCATION> {

	private final ILogger mLogger;
	private final IUltimateServiceProvider mServices;
	private final IHoareTripleChecker mHTC;
	private final ManagedScript mMgdScript;
	private final IIcfgSymbolTable mSymbolTable;
	private final SimplificationTechnique mSimplificationTechnique;

	private static int sIllegalPredicates = Integer.MAX_VALUE;

	public RcfgDebugHelper(final CfgSmtToolkit csToolkit, final IUltimateServiceProvider services,
			final IIcfgSymbolTable symbolTable) {
		mServices = services;
		mSymbolTable = symbolTable;
		mMgdScript = csToolkit.getManagedScript();
		mLogger = services.getLoggingService().getLogger(Activator.PLUGIN_ID);
		mSimplificationTechnique = SimplificationTechnique.SIMPLIFY_DDA;
		mHTC = new IncrementalHoareTripleChecker(csToolkit);
	}

	@Override
	public boolean isPostSound(final AbstractMultiState<STATE, ACTION, VARDECL> stateBeforeLeaving,
			final AbstractMultiState<STATE, ACTION, VARDECL> stateAfterLeaving,
			final AbstractMultiState<STATE, ACTION, VARDECL> postState, final ACTION transition) {
		final IPredicate precond = createPredicateFromState(stateBeforeLeaving);
		final IPredicate postcond = createPredicateFromState(postState);
		final IPredicate hierPre = getHierachicalPre(transition, () -> createPredicateFromState(stateAfterLeaving));
		return isPostSound(hierPre, transition, precond, postcond);
	}

	@Override
	public boolean isPostSound(final Set<STATE> statesBeforeLeaving, final Set<STATE> stateAfterLeaving,
			final Set<STATE> postStates, final ACTION transition) {
		final IPredicate precond = createPredicateFromState(statesBeforeLeaving);
		final IPredicate postcond = createPredicateFromState(postStates);
		final IPredicate hierPre = getHierachicalPre(transition, () -> createPredicateFromState(stateAfterLeaving));
		return isPostSound(hierPre, transition, precond, postcond);
	}

	private IPredicate getHierachicalPre(final ACTION transition, final Supplier<IPredicate> func) {
		if (transition instanceof IIcfgReturnTransition<?, ?>) {
			return func.get();
		}
		return null;
	}

	private boolean isPostSound(final IPredicate precondHier, final ACTION transition, final IPredicate precond,
			final IPredicate postcond) {
		final Validity result;
		if (transition instanceof Call) {
			result = mHTC.checkCall(precond, (ICallAction) transition, postcond);
		} else if (transition instanceof Return) {
			result = mHTC.checkReturn(precond, precondHier, (IReturnAction) transition, postcond);
		} else {
			result = mHTC.checkInternal(precond, (IInternalAction) transition, postcond);
		}
		mHTC.releaseLock();

		if (result != Validity.VALID) {
			logUnsoundness(transition, precond, postcond, precondHier);
		}
		return result != Validity.INVALID;
	}

	private void logUnsoundness(final ACTION transition, final IPredicate precond, final IPredicate postcond,
			final IPredicate precondHier) {
		mLogger.fatal("Soundness check failed for the following triple:");
		final String simplePre = SmtUtils
				.simplify(mMgdScript, precond.getFormula(), mServices, mSimplificationTechnique).toStringDirect();
		if (precondHier == null) {
			mLogger.fatal("Pre: {" + simplePre + "}");
		} else {
			mLogger.fatal("PreBefore: {" + simplePre + "}");
			mLogger.fatal("PreAfter: {"
					+ SmtUtils.simplify(mMgdScript, precondHier.getFormula(), mServices, mSimplificationTechnique)
							.toStringDirect()
					+ "}");
		}
		mLogger.fatal(getTransformulaDebugString(transition) + " (" + transition + ")");
		mLogger.fatal(
				"Post: {" + SmtUtils.simplify(mMgdScript, postcond.getFormula(), mServices, mSimplificationTechnique)
						.toStringDirect() + "}");
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

	private IPredicate createPredicateFromState(final Collection<STATE> states) {
		Term acc = mMgdScript.getScript().term("false");

		for (final STATE state : states) {
			acc = Util.or(mMgdScript.getScript(), acc, state.getTerm(mMgdScript.getScript()));
		}

		final TermVarsProc tvp = TermVarsProc.computeTermVarsProc(acc, mMgdScript.getScript(), mSymbolTable);
		return new BasicPredicate(getIllegalPredicateId(), tvp.getProcedures(), acc, tvp.getVars(),
				tvp.getClosedFormula());
	}

	private IPredicate createPredicateFromState(final AbstractMultiState<STATE, ACTION, VARDECL> state) {
		final Term acc = state.getTerm(mMgdScript.getScript());
		final TermVarsProc tvp = TermVarsProc.computeTermVarsProc(acc, mMgdScript.getScript(), mSymbolTable);
		return new BasicPredicate(getIllegalPredicateId(), tvp.getProcedures(), acc, tvp.getVars(),
				tvp.getClosedFormula());
	}

	private static int getIllegalPredicateId() {
		return sIllegalPredicates--;
	}
}
