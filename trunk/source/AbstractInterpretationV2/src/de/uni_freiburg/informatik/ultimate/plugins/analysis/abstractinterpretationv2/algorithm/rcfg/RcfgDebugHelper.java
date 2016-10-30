package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.rcfg;

import java.util.Collection;
import java.util.Set;
import java.util.function.Supplier;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Util;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Boogie2SmtSymbolTable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.ModifiableGlobalVariableManager;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.ICallAction;
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
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.model.IAbstractState;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;

/**
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 * @param <STATE>
 * @param <LOCATION>
 */
public class RcfgDebugHelper<STATE extends IAbstractState<STATE, CodeBlock, VARDECL>, VARDECL, LOCATION>
		implements IDebugHelper<STATE, CodeBlock, VARDECL, LOCATION> {

	private final ILogger mLogger;
	private final IUltimateServiceProvider mServices;
	private final IHoareTripleChecker mHTC;
	private final ManagedScript mMgdScript;
	private final Boogie2SmtSymbolTable mSymbolTable;
	private final SimplificationTechnique mSimplificationTechnique;

	private static int sIllegalPredicates = Integer.MAX_VALUE;

	public RcfgDebugHelper(final ManagedScript mgdScript, final ModifiableGlobalVariableManager modGlobVarMan,
			final IUltimateServiceProvider services, final Boogie2SmtSymbolTable symbolTable) {
		mServices = services;
		mSymbolTable = symbolTable;
		mMgdScript = mgdScript;
		mLogger = services.getLoggingService().getLogger(Activator.PLUGIN_ID);
		// TODO: Make parameter
		mSimplificationTechnique = SimplificationTechnique.SIMPLIFY_DDA;
		mHTC = new IncrementalHoareTripleChecker(mMgdScript, modGlobVarMan);
	}

	@Override
	public boolean isPostSound(final AbstractMultiState<STATE, CodeBlock, VARDECL> stateBeforeLeaving,
			final AbstractMultiState<STATE, CodeBlock, VARDECL> stateAfterLeaving,
			final AbstractMultiState<STATE, CodeBlock, VARDECL> postState, final CodeBlock transition) {
		final IPredicate precond = createPredicateFromState(stateBeforeLeaving);
		final IPredicate postcond = createPredicateFromState(postState);
		final IPredicate hierPre = getHierachicalPre(transition, () -> createPredicateFromState(stateAfterLeaving));
		return isPostSound(hierPre, transition, precond, postcond);
	}

	@Override
	public boolean isPostSound(final Set<STATE> statesBeforeLeaving, final Set<STATE> stateAfterLeaving,
			final Set<STATE> postStates, final CodeBlock transition) {
		final IPredicate precond = createPredicateFromState(statesBeforeLeaving);
		final IPredicate postcond = createPredicateFromState(postStates);
		final IPredicate hierPre = getHierachicalPre(transition, () -> createPredicateFromState(stateAfterLeaving));
		return isPostSound(hierPre, transition, precond, postcond);
	}

	private static IPredicate getHierachicalPre(final CodeBlock transition, final Supplier<IPredicate> func) {
		if (transition instanceof Return) {
			return func.get();
		}
		return null;
	}

	private boolean isPostSound(final IPredicate precondHier, final CodeBlock transition, final IPredicate precond,
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

	private void logUnsoundness(final CodeBlock transition, final IPredicate precond, final IPredicate postcond,
			final IPredicate precondHier) {
		mLogger.fatal("Soundness check failed for the following triple:");
		final String simplePre = SmtUtils
				.simplify(mMgdScript, precond.getFormula(), mServices, mSimplificationTechnique)
				.toStringDirect();
		if (precondHier == null) {
			mLogger.fatal("Pre: {" + simplePre + "}");
		} else {
			mLogger.fatal("PreBefore: {" + simplePre + "}");
			mLogger.fatal("PreAfter: {" + SmtUtils.simplify(mMgdScript, precondHier.getFormula(),
					mServices, mSimplificationTechnique).toStringDirect() + "}");
		}
		mLogger.fatal(transition.getTransitionFormula().getFormula().toStringDirect() + " (" + transition + ")");
		mLogger.fatal("Post: {" + SmtUtils
				.simplify(mMgdScript, postcond.getFormula(), mServices, mSimplificationTechnique)
				.toStringDirect() + "}");
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

	private IPredicate createPredicateFromState(final AbstractMultiState<STATE, CodeBlock, VARDECL> state) {
		final Term acc = state.getTerm(mMgdScript.getScript());
		final TermVarsProc tvp = TermVarsProc.computeTermVarsProc(acc, mMgdScript.getScript(), mSymbolTable);
		return new BasicPredicate(getIllegalPredicateId(), tvp.getProcedures(), acc, tvp.getVars(),
				tvp.getClosedFormula());
	}

	private static int getIllegalPredicateId() {
		return sIllegalPredicates--;
	}
}
