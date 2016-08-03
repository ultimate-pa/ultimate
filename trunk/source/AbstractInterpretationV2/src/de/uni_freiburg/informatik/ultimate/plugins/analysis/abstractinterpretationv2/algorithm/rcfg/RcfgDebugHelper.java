package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.rcfg;

import java.util.Collection;
import java.util.Collections;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Util;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Boogie2SMT;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.IBoogieVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.ICallAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IInternalAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IReturnAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hoaretriple.IHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hoaretriple.IHoareTripleChecker.Validity;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hoaretriple.IncrementalHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.SimplicationTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.BasicPredicate;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.TermVarsProc;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.IDebugHelper;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.model.IAbstractState;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootAnnot;

/**
 * 
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 * @param <STATE>
 * @param <LOCATION>
 */
public class RcfgDebugHelper<STATE extends IAbstractState<STATE, CodeBlock>, LOCATION>
		implements IDebugHelper<STATE, CodeBlock, IBoogieVar, LOCATION> {

	private final ILogger mLogger;
	private final IUltimateServiceProvider mServices;
	private final IHoareTripleChecker mHTC;
	private final Script mScript;
	private final Boogie2SMT mBoogie2Smt;
	private final SimplicationTechnique mSimplificationTechnique = SimplicationTechnique.SIMPLIFY_DDA;
	private final XnfConversionTechnique mXnfConversionTechnique = XnfConversionTechnique.BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION;

	private static int sIllegalPredicates = Integer.MAX_VALUE;

	public RcfgDebugHelper(final RootAnnot rootAnnot, final IUltimateServiceProvider services) {
		mServices = services;
		mScript = rootAnnot.getScript();
		mLogger = services.getLoggingService().getLogger(Activator.PLUGIN_ID);
		mBoogie2Smt = rootAnnot.getBoogie2SMT();
		mHTC = new IncrementalHoareTripleChecker(rootAnnot.getManagedScript(), rootAnnot.getModGlobVarManager());
	}

	@Override
	public boolean isPostSound(final STATE stateBeforeLeaving, final STATE stateAfterLeaving,
			final List<STATE> postStates, final CodeBlock transition) {
		final IPredicate precond = createPredicateFromState(Collections.singletonList(stateBeforeLeaving));
		final IPredicate postcond = createPredicateFromState(postStates);
		final IPredicate precondHier;
		final Validity result;

		if (transition instanceof Call) {
			precondHier = null;
			result = mHTC.checkCall(precond, (ICallAction) transition, postcond);
		} else if (transition instanceof Return) {
			precondHier = createPredicateFromState(Collections.singletonList(stateAfterLeaving));
			result = mHTC.checkReturn(precond, precondHier, (IReturnAction) transition, postcond);
		} else {
			precondHier = null;
			result = mHTC.checkInternal(precond, (IInternalAction) transition, postcond);
		}
		mHTC.releaseLock();

		if (result != Validity.VALID) {
			mLogger.fatal("Soundness check failed for the following triple:");
			final String simplePre = SmtUtils.simplify(mScript, precond.getFormula(), mServices, mSimplificationTechnique, mBoogie2Smt.getVariableManager()).toStringDirect();
			if (precondHier == null) {
				mLogger.fatal("Pre: {" + simplePre + "}");
			} else {
				mLogger.fatal("PreBefore: {" + simplePre + "}");
				mLogger.fatal("PreAfter: {"
						+ SmtUtils.simplify(mScript, precondHier.getFormula(), mServices, mSimplificationTechnique, mBoogie2Smt.getVariableManager()).toStringDirect() + "}");
			}
			mLogger.fatal(transition.getTransitionFormula().getFormula().toStringDirect());
			mLogger.fatal(
					"Post: {" + SmtUtils.simplify(mScript, postcond.getFormula(), mServices, mSimplificationTechnique, mBoogie2Smt.getVariableManager()).toStringDirect() + "}");
		}
		return result != Validity.INVALID;
	}

	private IPredicate createPredicateFromState(final Collection<STATE> states) {
		Term acc = mScript.term("false");

		for (final STATE state : states) {
			acc = Util.or(mScript, acc, state.getTerm(mScript, mBoogie2Smt));
		}

		final TermVarsProc tvp = TermVarsProc.computeTermVarsProc(acc, mScript, mBoogie2Smt.getBoogie2SmtSymbolTable());
		return new BasicPredicate(sIllegalPredicates--, tvp.getProcedures(), acc, tvp.getVars(),
				tvp.getClosedFormula());
	}
}
