/*
 * Copyright (C) 2016-2017 Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 * Copyright (C) 2017 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2016-2017 University of Freiburg
 *
 * This file is part of the ULTIMATE TraceAbstraction plug-in.
 *
 * The ULTIMATE TraceAbstraction plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TraceAbstraction plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceAbstraction plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceAbstraction plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TraceAbstraction plug-in grant you additional permission
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates;

import java.util.Objects;
import java.util.function.Consumer;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.absint.IAbstractDomain;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.absint.IAbstractPostOperator;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.absint.IAbstractState;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.absint.IAbstractState.SubsetResult;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.absint.IAbstractStateBinaryOperator;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.absint.IVariableProvider;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.IcfgUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.ICallAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgReturnTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IInternalAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IReturnAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hoaretriple.HoareTripleCheckerStatisticsGenerator;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hoaretriple.IHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hoaretriple.IncrementalHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.AbsIntPredicate;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;
import de.uni_freiburg.informatik.ultimate.util.InCaReCounter;

/**
 * {@link IHoareTripleChecker} that performs hoare triple checks using an abstract post operator.
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * @author Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 *
 */
public class AbsIntHoareTripleChecker<STATE extends IAbstractState<STATE, VARDECL>, ACTION extends IIcfgTransition<?>, VARDECL>
		implements IHoareTripleChecker {

	private final ILogger mLogger;
	private final IAbstractPostOperator<STATE, ACTION, VARDECL> mPostOp;
	private final IAbstractStateBinaryOperator<STATE> mMergeOp;
	private final IAbstractDomain<STATE, ACTION, VARDECL> mDomain;
	private final IPredicateUnifier mPredicateUnifier;
	private final HoareTripleCheckerStatisticsGenerator mBenchmark;
	private final IPredicate mTruePred;
	private final IPredicate mFalsePred;
	private final STATE mTopState;
	private final STATE mBottomState;
	private final IVariableProvider<STATE, ACTION, VARDECL> mVarProvider;
	private final IncrementalHoareTripleChecker mDebugHtc;
	private final IUltimateServiceProvider mServices;
	private final CfgSmtToolkit mCsToolkit;
	private final SimplificationTechnique mSimplificationTechnique;

	public AbsIntHoareTripleChecker(final ILogger logger, final IUltimateServiceProvider services,
			final IAbstractDomain<STATE, ACTION, VARDECL> domain,
			final IVariableProvider<STATE, ACTION, VARDECL> varProvider, final IPredicateUnifier predicateUnifer,
			final CfgSmtToolkit csToolkit) {
		mServices = services;
		mLogger = Objects.requireNonNull(logger);
		mDomain = Objects.requireNonNull(domain);
		mPostOp = Objects.requireNonNull(mDomain.getPostOperator());
		mMergeOp = Objects.requireNonNull(mDomain.getMergeOperator());
		mPredicateUnifier = Objects.requireNonNull(predicateUnifer);
		mVarProvider = Objects.requireNonNull(varProvider);
		mCsToolkit = Objects.requireNonNull(csToolkit);

		mSimplificationTechnique = SimplificationTechnique.SIMPLIFY_DDA;
		mBenchmark = new HoareTripleCheckerStatisticsGenerator();
		mTruePred = mPredicateUnifier.getTruePredicate();
		mFalsePred = mPredicateUnifier.getFalsePredicate();
		mTopState = mDomain.createTopState();
		mBottomState = mDomain.createBottomState();
		mDebugHtc = new IncrementalHoareTripleChecker(mCsToolkit);
	}

	@Override
	public void releaseLock() {
		// no lock needed
	}

	@Override
	public Validity checkInternal(final IPredicate pre, final IInternalAction act, final IPredicate succ) {
		return checkNonReturn(pre, act, succ);
	}

	@Override
	public Validity checkCall(final IPredicate pre, final ICallAction act, final IPredicate succ) {
		return checkNonReturn(pre, act, succ);
	}

	@Override
	public Validity checkReturn(final IPredicate preLinPred, final IPredicate preHierPred, final IReturnAction act,
			final IPredicate succPred) {
		mBenchmark.continueEdgeCheckerTime();

		final STATE preLin = getState(preLinPred);
		final STATE preHier = getState(preHierPred);
		final STATE succ = getState(succPred);
		final ACTION action = getAction(act);

		final Validity rtr = checkReturnTransition(preLin, preHier, action, succ);
		mBenchmark.stopEdgeCheckerTime();
		return rtr;
	}

	@Override
	public HoareTripleCheckerStatisticsGenerator getEdgeCheckerBenchmark() {
		return mBenchmark;
	}

	private Validity checkNonReturnTransition(final STATE origPreState, final ACTION act, final STATE origPostState) {
		final STATE preState = getValidState(origPreState, act);
		final STATE postState = getValidState(origPostState, act);
		final Validity result = checkNonReturnTransitionNoLogging(preState, act, postState);
		assert assertValidity(preState, null, act, postState, result);

		if (mLogger.isDebugEnabled()) {
			logDebugIfNotEqual(origPreState, preState, "Modified preState");
			logDebugIfNotEqual(origPostState, postState, "Modified postState");
			mLogger.debug("Pre : " + preState.toLogString());
			mLogger.debug("Act : " + act);
			mLogger.debug("Post: " + postState.toLogString());
			mLogger.debug("Result: " + result);
			mLogger.debug("--");
		}
		return result;
	}

	private Validity checkReturnTransition(final STATE origPreLinState, final STATE origPreHierState, final ACTION act,
			final STATE origPostState) {
		final STATE preLinState = getValidState(origPreLinState, act);
		final STATE preHierState = getValidPreHierstate(origPreHierState, act);
		final STATE postState = getValidState(origPostState, act);
		final Validity result = checkReturnTransitionNoLogging(preLinState, preHierState, act, postState);
		assert assertValidity(preLinState, preHierState, act, postState, result);
		if (mLogger.isDebugEnabled()) {
			logDebugIfNotEqual(origPreLinState, preLinState, "Modified preLinState");
			logDebugIfNotEqual(origPreHierState, preHierState, "Modified preHierState");
			logDebugIfNotEqual(origPostState, postState, "Modified postState");
			mLogger.debug("Pre : " + preLinState.toLogString());
			mLogger.debug("PreH: " + preHierState.toLogString());
			mLogger.debug("Act : " + act);
			mLogger.debug("Post: " + postState.toLogString());
			mLogger.debug("Result: " + result);
			mLogger.debug("--");
		}

		return result;
	}

	private void logDebugIfNotEqual(final STATE orig, final STATE modified, final String msg) {
		if (!modified.equals(orig)) {
			mLogger.debug(msg + ": " + modified.toLogString() + "(was: " + orig.toLogString() + ")");
		}
	}

	private Validity checkNonReturnTransitionNoLogging(final STATE preState, final ACTION act, final STATE postState) {
		if (preState.isBottom()) {
			return Validity.VALID;
		}

		final STATE calculatedPost = mPostOp.apply(preState, act).stream().reduce(mMergeOp::apply).orElse(null);
		if (postState.isBottom()) {
			if (calculatedPost != null && !calculatedPost.isBottom()) {
				return trackPost(Validity.INVALID, act);
			} else if (calculatedPost == null || calculatedPost.isBottom()) {
				return trackPost(Validity.VALID, act);
			}
		}

		final SubsetResult subs = calculatedPost.isSubsetOf(postState);
		if (subs != SubsetResult.NONE) {
			return trackPost(Validity.VALID, act);
		}
		return Validity.UNKNOWN;
	}

	private Validity checkReturnTransitionNoLogging(final STATE preLinState, final STATE preHierState, final ACTION act,
			final STATE postState) {

		if (preLinState.isBottom()) {
			return Validity.VALID;
		}

		if (preHierState.isBottom()) {
			return Validity.VALID;
		}

		final STATE calculatedPost =
				mPostOp.apply(preLinState, preHierState, act).stream().reduce(mMergeOp::apply).orElse(null);
		if (postState.isBottom()) {
			if (calculatedPost != null && !calculatedPost.isBottom()) {
				return trackPost(Validity.INVALID, act);
			} else if (calculatedPost == null || calculatedPost.isBottom()) {
				return trackPost(Validity.VALID, act);
			}
		}

		final SubsetResult subs = calculatedPost.isSubsetOf(postState);
		if (subs != SubsetResult.NONE) {
			return trackPost(Validity.VALID, act);
		}
		return Validity.UNKNOWN;
	}

	private Validity trackPost(final Validity valid, final ACTION act) {
		if (act instanceof ICallAction) {
			return trackPost(valid, InCaReCounter::incCa);
		} else if (act instanceof IReturnAction) {
			return trackPost(valid, InCaReCounter::incRe);
		} else {
			return trackPost(valid, InCaReCounter::incIn);
		}
	}

	private Validity trackPost(final Validity valid, final Consumer<InCaReCounter> inc) {
		if (valid == Validity.UNKNOWN) {
			inc.accept(mBenchmark.getSolverCounterUnknown());
		} else if (valid == Validity.VALID) {
			inc.accept(mBenchmark.getSolverCounterUnsat());
		} else if (valid == Validity.INVALID) {
			inc.accept(mBenchmark.getSolverCounterSat());
		}
		return valid;
	}

	@SuppressWarnings("unchecked")
	private STATE getState(final IPredicate pred) {
		if (pred instanceof AbsIntPredicate<?, ?>) {
			return ((AbsIntPredicate<STATE, ?>) pred).getAbstractState();
		} else if (pred.equals(mTruePred)) {
			return mTopState;
		} else if (pred.equals(mFalsePred)) {
			return mBottomState;
		} else {
			throw new UnsupportedOperationException("Cannot handle non-absint predicates: " + pred.getClass());
		}
	}

	@SuppressWarnings("unchecked")
	private ACTION getAction(final IAction act) {
		return (ACTION) act;
	}

	private Validity checkNonReturn(final IPredicate prePred, final IAction act, final IPredicate succPred) {
		mBenchmark.continueEdgeCheckerTime();
		final STATE pre = getState(prePred);
		final STATE succ = getState(succPred);
		final ACTION action = getAction(act);
		final Validity rtr = checkNonReturnTransition(pre, action, succ);
		mBenchmark.stopEdgeCheckerTime();
		return rtr;
	}

	private STATE getValidState(final STATE origPreState, final ACTION act) {
		final STATE rtr = mVarProvider.createValidState(act, origPreState);
		assert !origPreState.isBottom() || rtr.isBottom() : "Bottom was lost";
		return rtr;
	}

	@SuppressWarnings("unchecked")
	private STATE getValidPreHierstate(final STATE origPreHierState, final ACTION act) {
		if (act instanceof IIcfgReturnTransition<?, ?>) {
			final IIcfgReturnTransition<?, ?> retAct = (IIcfgReturnTransition<?, ?>) act;
			return getValidState(origPreHierState, (ACTION) retAct.getCorrespondingCall());
		}
		throw new UnsupportedOperationException("Cannot create hierprestate for non-return action: " + act.getClass());
	}

	private IPredicate createPredicateFromState(final STATE state) {
		final ManagedScript managedScript = mCsToolkit.getManagedScript();
		return mPredicateUnifier.getPredicateFactory().newPredicate(state.getTerm(managedScript.getScript()));
	}

	private boolean assertValidity(final STATE preLinState, final STATE preHierState, final ACTION transition,
			final STATE postState, final Validity result) {

		final IPredicate precond = createPredicateFromState(preLinState);
		final IPredicate postcond = createPredicateFromState(postState);
		final IPredicate precondHier;
		if (preHierState == null) {
			precondHier = null;
		} else {
			precondHier = createPredicateFromState(preHierState);
		}

		final Validity checkedResult = isPostSound(precond, precondHier, transition, postcond);
		if (checkedResult == result) {
			return true;
		}
		if (result == Validity.UNKNOWN) {
			return true;
		}
		mLogger.fatal("Check was " + result + " but should have been " + checkedResult);
		mLogger.fatal("Failing Hoare triple:");
		final String simplePre = SmtUtils
				.simplify(mCsToolkit.getManagedScript(), precond.getFormula(), mServices, mSimplificationTechnique)
				.toStringDirect();
		if (precondHier == null) {
			mLogger.fatal("Pre: {" + simplePre + "}");
		} else {
			mLogger.fatal("PreBefore: {" + simplePre + "}");
			mLogger.fatal("PreAfter: {" + SmtUtils.simplify(mCsToolkit.getManagedScript(), precondHier.getFormula(),
					mServices, mSimplificationTechnique).toStringDirect() + "}");
		}
		mLogger.fatal(
				IcfgUtils.getTransformula(transition).getClosedFormula().toStringDirect() + " (" + transition + ")");
		mLogger.fatal("Post: {" + SmtUtils
				.simplify(mCsToolkit.getManagedScript(), postcond.getFormula(), mServices, mSimplificationTechnique)
				.toStringDirect() + "}");
		return false;

	}

	private Validity isPostSound(final IPredicate precond, final IPredicate precondHier, final ACTION transition,
			final IPredicate postcond) {
		final Validity result;
		if (transition instanceof Call) {
			result = mDebugHtc.checkCall(precond, (ICallAction) transition, postcond);
		} else if (transition instanceof Return) {
			result = mDebugHtc.checkReturn(precond, precondHier, (IReturnAction) transition, postcond);
		} else {
			result = mDebugHtc.checkInternal(precond, (IInternalAction) transition, postcond);
		}
		mDebugHtc.releaseLock();
		return result;
	}

}
