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
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.absint.AbstractMultiState;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.absint.IAbstractDomain;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.absint.IAbstractPostOperator;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.absint.IAbstractState;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.absint.IAbstractState.SubsetResult;
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

	private static final String MSG_IS_SUBSET_OF_IS_UNSOUND = "isSubsetOf is unsound";
	private static final String MSG_TRACKED_VARIABLES_DIFFER = "Tracked variables differ";
	private static final String MSG_INVALID_HOARE_TRIPLE_CHECK = "Invalid hoare triple check";

	private final ILogger mLogger;
	private final IAbstractPostOperator<STATE, ACTION, VARDECL> mPostOp;
	private final IAbstractDomain<STATE, ACTION, VARDECL> mDomain;
	private final IPredicateUnifier mPredicateUnifier;
	private final HoareTripleCheckerStatisticsGenerator mBenchmark;
	private final IPredicate mTruePred;
	private final IPredicate mFalsePred;
	private final AbstractMultiState<STATE, ACTION, VARDECL> mTopState;
	private final AbstractMultiState<STATE, ACTION, VARDECL> mBottomState;
	private final IVariableProvider<STATE, ACTION, VARDECL> mVarProvider;
	private final IncrementalHoareTripleChecker mDebugHtc;
	private final IUltimateServiceProvider mServices;
	private final CfgSmtToolkit mCsToolkit;
	private final SimplificationTechnique mSimplificationTechnique;
	private final ManagedScript mManagedScript;

	public AbsIntHoareTripleChecker(final ILogger logger, final IUltimateServiceProvider services,
			final IAbstractDomain<STATE, ACTION, VARDECL> domain,
			final IVariableProvider<STATE, ACTION, VARDECL> varProvider, final IPredicateUnifier predicateUnifer,
			final CfgSmtToolkit csToolkit) {
		mServices = services;
		mLogger = Objects.requireNonNull(logger);
		mDomain = Objects.requireNonNull(domain);
		mPostOp = Objects.requireNonNull(mDomain.getPostOperator());
		mPredicateUnifier = Objects.requireNonNull(predicateUnifer);
		mVarProvider = Objects.requireNonNull(varProvider.createNewVariableProvider(csToolkit.getSymbolTable()));
		mCsToolkit = Objects.requireNonNull(csToolkit);
		mManagedScript = Objects.requireNonNull(mCsToolkit.getManagedScript());

		mSimplificationTechnique = SimplificationTechnique.SIMPLIFY_DDA;
		mBenchmark = new HoareTripleCheckerStatisticsGenerator();
		mTruePred = mPredicateUnifier.getTruePredicate();
		mFalsePred = mPredicateUnifier.getFalsePredicate();
		mTopState = new AbstractMultiState<>(5, mDomain.createTopState());
		mBottomState = new AbstractMultiState<>(5, mDomain.createBottomState());
		mDebugHtc = new IncrementalHoareTripleChecker(mCsToolkit);
	}

	@Override
	public void releaseLock() {
		// no lock needed
	}

	@Override
	public Validity checkInternal(final IPredicate prePred, final IInternalAction act, final IPredicate succPred) {
		mBenchmark.continueEdgeCheckerTime();
		final AbstractMultiState<STATE, ACTION, VARDECL> pre = getState(prePred);
		final AbstractMultiState<STATE, ACTION, VARDECL> succ = getState(succPred);
		final ACTION action = getAction(act);
		final AbstractMultiState<STATE, ACTION, VARDECL> preState =
				createValidPostOpStateAfterLeaving(action, pre, null);
		if (mLogger.isDebugEnabled()) {
			logDebugIfNotEqual(pre, preState, "Modified preState");
			mLogger.debug("Pre : " + preState.toLogString());
			mLogger.debug("Act : " + action);
			mLogger.debug("Post: " + succ.toLogString());
		}

		final Validity result = checkInternalTransitionWithValidState(preState, action, succ);
		if (mLogger.isDebugEnabled()) {
			mLogger.debug("Result: " + result);
		}
		assert assertValidity(preState, null, action, succ, result) : MSG_INVALID_HOARE_TRIPLE_CHECK;
		mLogger.debug("--");
		final Validity rtr = result;
		mBenchmark.stopEdgeCheckerTime();
		return rtr;
	}

	@Override
	public Validity checkCall(final IPredicate prePred, final ICallAction act, final IPredicate succPred) {
		mBenchmark.continueEdgeCheckerTime();
		final AbstractMultiState<STATE, ACTION, VARDECL> pre = getState(prePred);
		final AbstractMultiState<STATE, ACTION, VARDECL> succ = getState(succPred);
		final ACTION action = getAction(act);

		final AbstractMultiState<STATE, ACTION, VARDECL> preBeforeLeaving =
				createValidPostOpStateBeforeLeaving(action, pre);
		final AbstractMultiState<STATE, ACTION, VARDECL> preAfterLeaving =
				createValidPostOpStateAfterLeaving(action, pre, null);
		if (mLogger.isDebugEnabled()) {
			logDebugIfNotEqual(pre, preBeforeLeaving, "Modified PSBL");
			logDebugIfNotEqual(pre, preAfterLeaving, "Modified PSAL");
			mLogger.debug("PSBL : " + pre.toLogString());
			mLogger.debug("PSAL: " + preAfterLeaving.toLogString());
			mLogger.debug("Act : " + action);
			mLogger.debug("Post: " + succ.toLogString());
		}

		final Validity result =
				checkScopeChangingTransitionWithValidState(preBeforeLeaving, preAfterLeaving, action, succ);

		if (mLogger.isDebugEnabled()) {
			mLogger.debug("Result: " + result);
		}
		assert assertValidity(preBeforeLeaving, null, action, succ, result) : MSG_INVALID_HOARE_TRIPLE_CHECK;
		mLogger.debug("--");
		mBenchmark.stopEdgeCheckerTime();
		return result;
	}

	@Override
	public Validity checkReturn(final IPredicate preLinPred, final IPredicate preHierPred, final IReturnAction act,
			final IPredicate succPred) {
		mBenchmark.continueEdgeCheckerTime();

		final AbstractMultiState<STATE, ACTION, VARDECL> preLin = getState(preLinPred);
		final AbstractMultiState<STATE, ACTION, VARDECL> preHier = getState(preHierPred);
		final AbstractMultiState<STATE, ACTION, VARDECL> succ = getState(succPred);
		final ACTION action = getAction(act);
		assert action instanceof IIcfgReturnTransition<?, ?>;
		final IIcfgReturnTransition<?, ?> retAct = (IIcfgReturnTransition<?, ?>) action;
		final ACTION correspondingCall = (ACTION) retAct.getCorrespondingCall();

		final AbstractMultiState<STATE, ACTION, VARDECL> validPreLinState =
				createValidPostOpStateBeforeLeaving(action, preLin);
		final AbstractMultiState<STATE, ACTION, VARDECL> validPreHierState =
				createValidPostOpStateBeforeLeaving(correspondingCall, preHier);
		final AbstractMultiState<STATE, ACTION, VARDECL> stateAfterLeaving =
				createValidPostOpStateAfterLeaving(action, validPreLinState, validPreHierState);
		if (mLogger.isDebugEnabled()) {
			logDebugIfNotEqual(preLin, validPreLinState, "Modified preLinState");
			logDebugIfNotEqual(preHier, validPreHierState, "Modified preHierState");
			mLogger.debug("Pre : " + validPreLinState.toLogString());
			mLogger.debug("PreH: " + validPreHierState.toLogString());
			mLogger.debug("PSAL: " + stateAfterLeaving.toLogString());
			mLogger.debug("Act : (" + action.getPrecedingProcedure() + ") " + action + " ("
					+ action.getSucceedingProcedure() + ")");
			mLogger.debug("Post: " + succ.toLogString());
		}

		final Validity result =
				checkScopeChangingTransitionWithValidState(validPreLinState, stateAfterLeaving, action, succ);
		if (mLogger.isDebugEnabled()) {
			mLogger.debug("Result: " + result);
		}
		assert assertValidity(validPreLinState, stateAfterLeaving, action, succ,
				result) : MSG_INVALID_HOARE_TRIPLE_CHECK;
		mLogger.debug("--");
		final Validity rtr = result;
		mBenchmark.stopEdgeCheckerTime();
		return rtr;
	}

	@Override
	public HoareTripleCheckerStatisticsGenerator getEdgeCheckerBenchmark() {
		return mBenchmark;
	}

	private Validity checkInternalTransitionWithValidState(final AbstractMultiState<STATE, ACTION, VARDECL> preState,
			final ACTION act, final AbstractMultiState<STATE, ACTION, VARDECL> postState) {
		if (preState.isBottom()) {
			return Validity.VALID;
		}

		final AbstractMultiState<STATE, ACTION, VARDECL> calculatedPost = preState.apply(mPostOp, act);
		return comparePostAndCalculatedPost(act, postState, calculatedPost);
	}

	private Validity checkScopeChangingTransitionWithValidState(
			final AbstractMultiState<STATE, ACTION, VARDECL> stateBeforeLeaving,
			final AbstractMultiState<STATE, ACTION, VARDECL> stateAfterLeaving, final ACTION act,
			final AbstractMultiState<STATE, ACTION, VARDECL> postState) {

		if (stateBeforeLeaving.isBottom()) {
			return Validity.VALID;
		}

		if (stateAfterLeaving.isBottom()) {
			return Validity.VALID;
		}

		final AbstractMultiState<STATE, ACTION, VARDECL> calculatedPost =
				stateAfterLeaving.apply(mPostOp, stateBeforeLeaving, act);
		return comparePostAndCalculatedPost(act, postState, calculatedPost);
	}

	private Validity comparePostAndCalculatedPost(final ACTION act,
			final AbstractMultiState<STATE, ACTION, VARDECL> postState,
			final AbstractMultiState<STATE, ACTION, VARDECL> calculatedPost) {
		if (mLogger.isDebugEnabled()) {
			mLogger.debug("Calculated post: " + calculatedPost.toLogString());
		}
		if (calculatedPost.isBottom() && postState.isBottom()) {
			return trackPost(Validity.VALID, act);
		}

		final AbstractMultiState<STATE, ACTION, VARDECL> synchronizedCalculatedPost =
				synchronizeState(postState, calculatedPost);
		if (mLogger.isDebugEnabled()) {
			mLogger.debug("Synchronized calculated post: " + calculatedPost.toLogString());
		}
		assert synchronizedCalculatedPost.isBottom() || postState.getVariables()
				.equals(synchronizedCalculatedPost.getVariables()) : MSG_TRACKED_VARIABLES_DIFFER;
		final SubsetResult included = synchronizedCalculatedPost.isSubsetOf(postState);
		assert assertIsSubsetOf(synchronizedCalculatedPost, postState, included) : MSG_IS_SUBSET_OF_IS_UNSOUND;
		if (mLogger.isDebugEnabled()) {
			mLogger.debug("Inclusion (NO): " + included);

		}
		if (included != SubsetResult.NONE) {
			return trackPost(Validity.VALID, act);
		}
		final SubsetResult excluded = postState.isSubsetOf(synchronizedCalculatedPost);
		assert assertIsSubsetOf(postState, synchronizedCalculatedPost, included) : MSG_IS_SUBSET_OF_IS_UNSOUND;
		if (mLogger.isDebugEnabled()) {
			mLogger.debug("Exclusion (ON): " + excluded);
		}
		if (excluded == SubsetResult.NONE) {
			assert !synchronizedCalculatedPost.isBottom() : "Nothing is a subset of bottom";
			return trackPost(Validity.INVALID, act);
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
	private AbstractMultiState<STATE, ACTION, VARDECL> getState(final IPredicate pred) {
		if (pred instanceof AbsIntPredicate<?, ?>) {
			return new AbstractMultiState<>(((AbsIntPredicate<STATE, ?>) pred).getAbstractStates());
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

	private AbstractMultiState<STATE, ACTION, VARDECL> synchronizeState(
			final AbstractMultiState<STATE, ACTION, VARDECL> template,
			final AbstractMultiState<STATE, ACTION, VARDECL> toSynchronize) {
		final AbstractMultiState<STATE, ACTION, VARDECL> rtr =
				template.synchronizeVariables(mVarProvider, toSynchronize);
		assert !toSynchronize.isBottom() || rtr.isBottom() : "Bottom was lost";
		return rtr;
	}

	private AbstractMultiState<STATE, ACTION, VARDECL> createValidPostOpStateAfterLeaving(final ACTION act,
			final AbstractMultiState<STATE, ACTION, VARDECL> pre,
			final AbstractMultiState<STATE, ACTION, VARDECL> preHierState) {

		final AbstractMultiState<STATE, ACTION, VARDECL> rtr =
				pre.createValidPostOpStateAfterLeaving(mVarProvider, act, preHierState);
		assert !pre.isBottom() && (preHierState == null || !preHierState.isBottom())
				|| rtr.isBottom() : "Bottom was lost";
		return rtr;
	}

	private AbstractMultiState<STATE, ACTION, VARDECL> createValidPostOpStateBeforeLeaving(final ACTION act,
			final AbstractMultiState<STATE, ACTION, VARDECL> preLin) {

		final AbstractMultiState<STATE, ACTION, VARDECL> rtr =
				preLin.createValidPostOpStateBeforeLeaving(mVarProvider, act);
		assert !preLin.isBottom() || rtr.isBottom() : "Bottom was lost";
		return rtr;
	}

	private void logDebugIfNotEqual(final AbstractMultiState<STATE, ACTION, VARDECL> pre,
			final AbstractMultiState<STATE, ACTION, VARDECL> preState, final String msg) {
		if (!preState.equals(pre)) {
			mLogger.debug(msg + ": " + preState.toLogString() + "(was: " + pre.toLogString() + ")");
		}
	}

	private IPredicate createPredicateFromState(final AbstractMultiState<STATE, ACTION, VARDECL> preState) {
		return mPredicateUnifier.getPredicateFactory().newPredicate(preState.getTerm(mManagedScript.getScript()));
	}

	private boolean assertValidity(final AbstractMultiState<STATE, ACTION, VARDECL> preState,
			final AbstractMultiState<STATE, ACTION, VARDECL> validPreLinState, final ACTION transition,
			final AbstractMultiState<STATE, ACTION, VARDECL> succ, final Validity result) {

		final IPredicate precond = createPredicateFromState(preState);
		final IPredicate postcond = createPredicateFromState(succ);
		final IPredicate precondHier;
		if (validPreLinState == null) {
			precondHier = null;
		} else {
			precondHier = createPredicateFromState(validPreLinState);
		}

		final Validity checkedResult = assertIsPostSound(precond, precondHier, transition, postcond);
		if (checkedResult == result) {
			mLogger.debug("HTC assert ok");
			return true;
		}
		if (result == Validity.UNKNOWN || result == Validity.NOT_CHECKED) {
			mLogger.debug("HTC assert ok");
			return true;
		}
		mLogger.fatal("Check was " + result + " but should have been " + checkedResult);
		mLogger.fatal("Failing Hoare triple:");
		final String simplePre = SmtUtils
				.simplify(mManagedScript, precond.getFormula(), mServices, mSimplificationTechnique).toStringDirect();
		if (precondHier == null) {
			mLogger.fatal("Pre: {" + simplePre + "}");
		} else {
			mLogger.fatal("PreBefore: {" + simplePre + "}");
			mLogger.fatal("PreAfter: {"
					+ SmtUtils.simplify(mManagedScript, precondHier.getFormula(), mServices, mSimplificationTechnique)
							.toStringDirect()
					+ "}");
		}
		mLogger.fatal(
				IcfgUtils.getTransformula(transition).getClosedFormula().toStringDirect() + " (" + transition + ")");
		mLogger.fatal("Post: {" + SmtUtils
				.simplify(mManagedScript, postcond.getFormula(), mServices, mSimplificationTechnique).toStringDirect()
				+ "}");
		return false;

	}

	private Validity assertIsPostSound(final IPredicate precond, final IPredicate precondHier, final ACTION transition,
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

	private boolean assertIsSubsetOf(final AbstractMultiState<STATE, ACTION, VARDECL> leftState,
			final AbstractMultiState<STATE, ACTION, VARDECL> rightState, final SubsetResult subResult) {
		final Script script = mManagedScript.getScript();
		final Term left = leftState.getTerm(script);
		final Term right = rightState.getTerm(script);

		final LBool result;
		final LBool expected;
		final Term checkedTerm;
		switch (subResult) {
		case EQUAL:
			checkedTerm = script.term("distinct", left, right);
			expected = LBool.UNSAT;
			result = SmtUtils.checkSatTerm(script, checkedTerm);
			break;
		case NONE:
			checkedTerm = script.term("and", script.term("=>", right, left), script.term("=>", left, right));
			expected = LBool.UNSAT;
			result = SmtUtils.checkSatTerm(script, checkedTerm);
			break;
		case NON_STRICT:
		case STRICT:
			checkedTerm = script.term("=>", right, left);
			expected = LBool.SAT;
			result = SmtUtils.checkSatTerm(script, checkedTerm);
			break;
		default:
			throw new UnsupportedOperationException("Unsupported subset result: " + subResult);
		}

		if (result == LBool.UNKNOWN || result == expected) {
			return true;
		}

		if (mLogger.isDebugEnabled()) {
			final Term leftSimpl =
					SmtUtils.simplify(mManagedScript, left, mServices, SimplificationTechnique.SIMPLIFY_DDA);
			final Term rightSimpl =
					SmtUtils.simplify(mManagedScript, right, mServices, SimplificationTechnique.SIMPLIFY_DDA);
			final Term checkSimpl =
					SmtUtils.simplify(mManagedScript, checkedTerm, mServices, SimplificationTechnique.SIMPLIFY_DDA);

			mLogger.debug("Checking left isSubsetOrEqual right = " + subResult);
			mLogger.debug("leftState  : " + leftState.toLogString());
			mLogger.debug("rightState : " + rightState.toLogString());
			mLogger.debug("left       : " + left.toStringDirect());
			mLogger.debug("right      : " + right.toStringDirect());
			mLogger.debug("leftSim    : " + leftSimpl.toStringDirect());
			mLogger.debug("rightSim   : " + rightSimpl.toStringDirect());
			mLogger.debug("checking   : " + checkedTerm.toStringDirect());
			mLogger.debug("checkingSim: " + checkSimpl.toStringDirect());
			mLogger.debug("Result is " + result + " and should be " + expected);
		}

		final SubsetResult reComputeForDebug = leftState.isSubsetOf(rightState);
		mLogger.debug(reComputeForDebug);
		return false;
	}

}
