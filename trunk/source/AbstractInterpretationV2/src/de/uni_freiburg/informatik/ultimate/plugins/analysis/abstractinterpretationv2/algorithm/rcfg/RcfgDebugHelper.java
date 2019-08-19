package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.rcfg;

import java.util.function.Supplier;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.DisjunctiveAbstractState;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractState;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.ICallAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgReturnTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IInternalAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IReturnAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.DebuggingHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.IHoareTripleChecker.Validity;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.AbsIntPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.BasicPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.TermVarsProc;
import de.uni_freiburg.informatik.ultimate.logic.Term;
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

	private final ILogger mLogger;
	private final IUltimateServiceProvider mServices;
	private final DebuggingHoareTripleChecker mHTC;
	private final ManagedScript mMgdScript;
	private final IIcfgSymbolTable mSymbolTable;

	private static int sIllegalPredicates = Integer.MAX_VALUE;

	public RcfgDebugHelper(final CfgSmtToolkit csToolkit, final IUltimateServiceProvider services,
			final IIcfgSymbolTable symbolTable) {
		mServices = services;
		mSymbolTable = symbolTable;
		mMgdScript = csToolkit.getManagedScript();
		mLogger = services.getLoggingService().getLogger(Activator.PLUGIN_ID);
		mHTC = new DebuggingHoareTripleChecker(mServices, mLogger, csToolkit, Validity.VALID);
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
			if (transition instanceof ICallAction) {
				mHTC.checkCall(precond, (ICallAction) transition, postcond);
			} else if (transition instanceof IReturnAction) {
				mHTC.checkReturn(precond, precondHier, (IReturnAction) transition, postcond);
			} else {
				mHTC.checkInternal(precond, (IInternalAction) transition, postcond);
			}
			return mHTC.isLastOk();
		} finally {
			mHTC.releaseLock();
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
