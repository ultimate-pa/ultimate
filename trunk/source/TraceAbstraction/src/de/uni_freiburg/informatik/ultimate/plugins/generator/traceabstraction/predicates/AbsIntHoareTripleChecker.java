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

import java.util.HashSet;
import java.util.Objects;
import java.util.Set;
import java.util.function.Consumer;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.QuotedObject;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.absint.DisjunctiveAbstractState;
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
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramOldVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hoaretriple.DebuggingHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hoaretriple.HoareTripleCheckerStatisticsGenerator;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hoaretriple.IHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hoaretriple.IncrementalHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.AbsIntPredicate;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.util.AbsIntUtil;
import de.uni_freiburg.informatik.ultimate.util.InCaReCounter;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;

/**
 * {@link IHoareTripleChecker} that performs hoare triple checks using an abstract post operator.
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * @author Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 *
 */
public class AbsIntHoareTripleChecker<STATE extends IAbstractState<STATE>, ACTION extends IIcfgTransition<?>>
		implements IHoareTripleChecker {

	private static final int MAX_DISJUNCTS = 1;
	private static final boolean ACCEPT_REJECTION_DUE_TO_IMPRECISION = true;
	/**
	 * 2018-09-06 DD: This flag is a hack. Try to reduce states based on the variables occurring in the transformula.
	 * Only works correctly if transformulas were used during the analysis.
	 *
	 * The correct solution would be the usage of the analysis settings to determine this flag.
	 *
	 */
	private static final boolean REDUCE_STATES = true;

	private static final String MSG_BOTTOM_WAS_LOST = "Bottom was lost";
	private static final String MSG_IS_SUBSET_OF_IS_UNSOUND = "isSubsetOf is unsound";
	private static final String MSG_TRACKED_VARIABLES_DIFFER = "Tracked variables differ";
	private static final String MSG_INVALID_HOARE_TRIPLE_CHECK = "Invalid AbsInt hoare triple check";

	private final ILogger mLogger;
	private final IAbstractPostOperator<STATE, ACTION> mPostOp;
	private final IAbstractDomain<STATE, ACTION> mDomain;
	private final IPredicateUnifier mPredicateUnifier;
	private final HoareTripleCheckerStatisticsGenerator mBenchmark;
	private final IPredicate mTruePred;
	private final IPredicate mFalsePred;
	private final DisjunctiveAbstractState<STATE> mTopState;
	private final DisjunctiveAbstractState<STATE> mBottomState;
	private final IVariableProvider<STATE, ACTION> mVarProvider;
	private final IncrementalHoareTripleChecker mHtcSmt;
	private final IUltimateServiceProvider mServices;
	private final CfgSmtToolkit mCsToolkit;
	private final SimplificationTechnique mSimplificationTechnique;
	private final ManagedScript mManagedScript;
	private final SdHoareTripleChecker mHtcSd;
	private final boolean mOnlyAbsInt;
	private final boolean mUseHierachicalPre;

	/**
	 * Create a new {@link AbsIntHoareTripleChecker} instance.
	 *
	 * @param logger
	 *            An {@link ILogger} instance
	 * @param services
	 *            An {@link IUltimateServiceProvider} instance
	 * @param domain
	 *            The {@link IAbstractDomain} that should be used for the hoare triple checks (it must be the domain
	 *            that created the abstract states)
	 * @param varProvider
	 *            A {@link IVariableProvider} that supports all {@link IAction}s that will be seen by this hoare triple
	 *            checker.
	 * @param predicateUnifer
	 *            A {@link IPredicateUnifier} that is only used during assertions and as supplier of true and false
	 *            predicates
	 * @param csToolkit
	 *            A {@link CfgSmtToolkit} which is used for fallback HTC checks with SMT-based hoare triple checkers
	 * @param onlyAbsInt
	 *            A flag controlling whether this HTC falls back to SMT-based hoare triple checkers (false) or not
	 *            (true).
	 */
	public AbsIntHoareTripleChecker(final ILogger logger, final IUltimateServiceProvider services,
			final IAbstractDomain<STATE, ACTION> domain, final IVariableProvider<STATE, ACTION> varProvider,
			final IPredicateUnifier predicateUnifer, final CfgSmtToolkit csToolkit, final boolean onlyAbsInt) {
		mServices = services;
		mLogger = Objects.requireNonNull(logger);
		mDomain = Objects.requireNonNull(domain);
		mUseHierachicalPre = mDomain.useHierachicalPre();

		mPostOp = Objects.requireNonNull(mDomain.getPostOperator());
		mPredicateUnifier = Objects.requireNonNull(predicateUnifer);
		mVarProvider = Objects.requireNonNull(varProvider.createNewVariableProvider(csToolkit));
		mCsToolkit = Objects.requireNonNull(csToolkit);
		mManagedScript = Objects.requireNonNull(mCsToolkit.getManagedScript());

		mSimplificationTechnique = SimplificationTechnique.SIMPLIFY_DDA;
		mBenchmark = new HoareTripleCheckerStatisticsGenerator();
		mTruePred = mPredicateUnifier.getTruePredicate();
		mFalsePred = mPredicateUnifier.getFalsePredicate();
		mTopState = new DisjunctiveAbstractState<>(MAX_DISJUNCTS, mDomain.createTopState());
		mBottomState = new DisjunctiveAbstractState<>(MAX_DISJUNCTS, mDomain.createBottomState());
		mHtcSmt = new IncrementalHoareTripleChecker(mCsToolkit, false);
		mHtcSd = new SdHoareTripleChecker(mCsToolkit, predicateUnifer, mBenchmark);
		mOnlyAbsInt = onlyAbsInt;

	}

	@Override
	public void releaseLock() {
		// no lock needed
	}

	@Override
	public Validity checkInternal(final IPredicate prePred, final IInternalAction act, final IPredicate succPred) {
		if (mOnlyAbsInt) {
			return checkInternalAbsInt(prePred, act, succPred);
		}
		final Validity sdResult = mHtcSd.checkInternal(prePred, act, succPred);
		if (isFinalResult(sdResult)) {
			return sdResult;
		}
		final Validity absIntResult = checkInternalAbsInt(prePred, act, succPred);
		if (absIntResult == Validity.VALID) {
			return absIntResult;
		}
		final Validity result = mHtcSmt.checkInternal(prePred, act, succPred);
		mHtcSmt.releaseLock();
		return result;
	}

	@Override
	public Validity checkCall(final IPredicate prePred, final ICallAction act, final IPredicate succPred) {
		if (mOnlyAbsInt) {
			return checkCallAbsInt(prePred, act, succPred);
		}
		final Validity sdResult = mHtcSd.checkCall(prePred, act, succPred);
		mHtcSd.releaseLock();
		if (isFinalResult(sdResult)) {
			return sdResult;
		}
		final Validity absIntResult = checkCallAbsInt(prePred, act, succPred);
		if (absIntResult == Validity.VALID) {
			return absIntResult;
		}
		final Validity result = mHtcSmt.checkCall(prePred, act, succPred);
		mHtcSmt.releaseLock();
		return result;
	}

	@Override
	public Validity checkReturn(final IPredicate preLinPred, final IPredicate preHierPred, final IReturnAction act,
			final IPredicate succPred) {
		if (mOnlyAbsInt) {
			return checkReturnAbsInt(preLinPred, preHierPred, act, succPred);
		}
		final Validity sdResult = mHtcSd.checkReturn(preLinPred, preHierPred, act, succPred);
		if (isFinalResult(sdResult)) {
			return sdResult;
		}
		final Validity absIntResult = checkReturnAbsInt(preLinPred, preHierPred, act, succPred);
		if (absIntResult == Validity.VALID) {
			return absIntResult;
		}
		final Validity result = mHtcSmt.checkReturn(preLinPred, preHierPred, act, succPred);
		mHtcSmt.releaseLock();
		return result;
	}

	private static boolean isFinalResult(final Validity result) {
		return result != Validity.UNKNOWN && result != Validity.NOT_CHECKED;
	}

	private Validity checkInternalAbsInt(final IPredicate prePred, final IInternalAction act,
			final IPredicate succPred) {
		mBenchmark.continueEdgeCheckerTime();
		final DisjunctiveAbstractState<STATE> pre = getState(prePred);
		final DisjunctiveAbstractState<STATE> succ = getState(succPred);
		final ACTION action = getAction(act);

		final DisjunctiveAbstractState<STATE> validPreState = createValidPostOpStateAfterLeaving(action, pre, null);
		final DisjunctiveAbstractState<STATE> reducedPostState = succ.compact();
		final DisjunctiveAbstractState<STATE> reducedPreState = reducePreState(validPreState, reducedPostState, action);

		if (mLogger.isDebugEnabled()) {
			mLogger.debug("Pre : " + reducedPreState.toLogString());
			mLogger.debug("Act : " + action);
			mLogger.debug("Post: " + reducedPostState.toLogString());
		}

		final Validity result = checkInternalTransitionWithValidState(reducedPreState, action, reducedPostState);
		if (mLogger.isDebugEnabled()) {
			mLogger.debug(getMsgResult(result));
		}
		assert assertValidity(validPreState, null, action, succ, result) : MSG_INVALID_HOARE_TRIPLE_CHECK;
		mLogger.debug("--");
		final Validity rtr = result;
		mBenchmark.stopEdgeCheckerTime();
		return rtr;
	}

	private static String getMsgResult(final Validity result) {
		return "Result: " + result;
	}

	private Set<IProgramVarOrConst> getVars(final ACTION action) {
		return mVarProvider.getRequiredVars(action);
	}

	private Validity checkCallAbsInt(final IPredicate prePred, final ICallAction act, final IPredicate succPred) {
		mBenchmark.continueEdgeCheckerTime();
		final DisjunctiveAbstractState<STATE> pre = getState(prePred);
		final DisjunctiveAbstractState<STATE> succ = getState(succPred);
		final ACTION action = getAction(act);

		final DisjunctiveAbstractState<STATE> validPreBL = createValidPostOpStateBeforeLeaving(action, pre);
		final DisjunctiveAbstractState<STATE> validPreAL = createValidPostOpStateAfterLeaving(action, pre, null);
		final DisjunctiveAbstractState<STATE> reducedPreBL = reducePreState(validPreBL, succ, action);
		final DisjunctiveAbstractState<STATE> reducedPreAL = reducePreState(validPreAL, succ, action);
		if (mLogger.isDebugEnabled()) {
			mLogger.debug("PSBL: " + reducedPreBL.toLogString());
			mLogger.debug("PSAL: " + reducedPreAL.toLogString());
			mLogger.debug("Act : " + action);
			mLogger.debug("Post: " + succ.toLogString());
		}

		final Validity result = checkScopeChangingTransitionWithValidState(reducedPreBL, reducedPreAL, action, succ);
		if (mLogger.isDebugEnabled()) {
			mLogger.debug(getMsgResult(result));
		}
		assert assertValidity(validPreBL, null, action, succ, result) : MSG_INVALID_HOARE_TRIPLE_CHECK;
		mLogger.debug("--");
		mBenchmark.stopEdgeCheckerTime();
		return result;
	}

	private Validity checkReturnAbsInt(final IPredicate preLinPred, final IPredicate preHierPred,
			final IReturnAction act, final IPredicate succPred) {
		mBenchmark.continueEdgeCheckerTime();

		final DisjunctiveAbstractState<STATE> pre = getState(preLinPred);
		final DisjunctiveAbstractState<STATE> preHier = getState(preHierPred);
		final DisjunctiveAbstractState<STATE> succ = getState(succPred);
		final ACTION action = getAction(act);
		final ACTION correspondingCall = getCorrespondingCall(action);

		final DisjunctiveAbstractState<STATE> validPreBL = createValidPostOpStateBeforeLeaving(action, pre);
		final DisjunctiveAbstractState<STATE> validPreHier =
				createValidPostOpStateBeforeLeaving(correspondingCall, preHier);
		final DisjunctiveAbstractState<STATE> validPreAL;
		if (mUseHierachicalPre) {
			validPreAL = createValidPostOpStateHierachicalPre(validPreBL, validPreHier);
		} else {
			validPreAL = createValidPostOpStateAfterLeaving(action, validPreBL, validPreHier);
		}

		if (mLogger.isDebugEnabled()) {
			mLogger.debug("PreBL: " + validPreBL.toLogString());
			mLogger.debug("PreH : " + validPreHier.toLogString());
			mLogger.debug("PreAL: " + validPreAL.toLogString());
			mLogger.debug("Act  : (" + action.getPrecedingProcedure() + ") " + action + " ("
					+ action.getSucceedingProcedure() + ")");
			mLogger.debug("Post : " + succ.toLogString());
		}

		final Validity result = checkScopeChangingTransitionWithValidState(validPreBL, validPreAL, action, succ);
		if (mLogger.isDebugEnabled()) {
			mLogger.debug(getMsgResult(result));
		}
		assert assertValidity(validPreBL, validPreAL, action, succ, result) : MSG_INVALID_HOARE_TRIPLE_CHECK;
		mLogger.debug("--");
		final Validity rtr = result;
		mBenchmark.stopEdgeCheckerTime();
		return rtr;
	}

	private ACTION getCorrespondingCall(final ACTION action) {
		assert action instanceof IIcfgReturnTransition<?, ?>;
		final IIcfgReturnTransition<?, ?> retAct = (IIcfgReturnTransition<?, ?>) action;
		return (ACTION) retAct.getCorrespondingCall();
	}

	@Override
	public HoareTripleCheckerStatisticsGenerator getEdgeCheckerBenchmark() {
		return mBenchmark;
	}

	private Validity checkInternalTransitionWithValidState(final DisjunctiveAbstractState<STATE> preState,
			final ACTION act, final DisjunctiveAbstractState<STATE> postState) {
		if (preState.isBottom()) {
			return Validity.VALID;
		}

		final DisjunctiveAbstractState<STATE> calculatedPost = preState.apply(mPostOp, act);
		return comparePostAndCalculatedPost(act, postState, calculatedPost);
	}

	private Validity checkScopeChangingTransitionWithValidState(
			final DisjunctiveAbstractState<STATE> stateBeforeLeaving,
			final DisjunctiveAbstractState<STATE> stateAfterLeaving, final ACTION act,
			final DisjunctiveAbstractState<STATE> postState) {

		if (stateBeforeLeaving.isBottom()) {
			return Validity.VALID;
		}

		if (stateAfterLeaving.isBottom()) {
			return Validity.VALID;
		}

		// TODO: Take mDomain.useHierachicalPre() into account (this is relevant for PredicateTransformer based domains
		// like the EQ domain; those are probably legacy anyways)
		final DisjunctiveAbstractState<STATE> calculatedPost =
				stateAfterLeaving.apply(mPostOp, stateBeforeLeaving, act);
		return comparePostAndCalculatedPost(act, postState, calculatedPost);
	}

	private Validity comparePostAndCalculatedPost(final ACTION act, final DisjunctiveAbstractState<STATE> postState,
			final DisjunctiveAbstractState<STATE> calculatedPost) {
		if (mLogger.isDebugEnabled()) {
			mLogger.debug("Calculated post: " + calculatedPost.toLogString());
		}
		if (calculatedPost.isBottom() && postState.isBottom()) {
			return trackPost(Validity.VALID, act);
		}

		final DisjunctiveAbstractState<STATE> synchronizedCalculatedPost = synchronizeState(postState, calculatedPost);
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
		assert assertIsSubsetOf(postState, synchronizedCalculatedPost, excluded) : MSG_IS_SUBSET_OF_IS_UNSOUND;
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
	private DisjunctiveAbstractState<STATE> getState(final IPredicate pred) {
		if (pred instanceof AbsIntPredicate<?>) {
			final Set<STATE> states = ((AbsIntPredicate<STATE>) pred).getAbstractStates();
			if (states.size() <= 1) {
				return DisjunctiveAbstractState.createDisjunction(states);
			}
			final Set<IProgramVarOrConst> vars = new HashSet<>();
			states.stream().forEach(a -> vars.addAll(a.getVariables()));
			final Set<STATE> synchronizedStates =
					states.stream().map(a -> AbsIntUtil.synchronizeVariables(a, vars)).collect(Collectors.toSet());
			return DisjunctiveAbstractState.createDisjunction(synchronizedStates);
		} else if (pred.equals(mTruePred)) {
			return mTopState;
		} else if (pred.equals(mFalsePred)) {
			return mBottomState;
		} else {
			throw new UnsupportedOperationException(
					"Cannot handle non-absint predicates: " + pred.hashCode() + " (" + pred.getClass() + ")");
		}
	}

	@SuppressWarnings("unchecked")
	private ACTION getAction(final IAction act) {
		return (ACTION) act;
	}

	private DisjunctiveAbstractState<STATE> synchronizeState(final DisjunctiveAbstractState<STATE> template,
			final DisjunctiveAbstractState<STATE> toSynchronize) {

		final DisjunctiveAbstractState<STATE> unifiedToSynchronize = unifyBottom(toSynchronize);
		if (unifiedToSynchronize == mBottomState) {
			return unifiedToSynchronize;
		}
		final DisjunctiveAbstractState<STATE> rtr = AbsIntUtil.synchronizeVariables(template, unifiedToSynchronize);
		assert assertBottomRetained(unifiedToSynchronize, null, rtr,
				() -> AbsIntUtil.synchronizeVariables(template, unifiedToSynchronize)) : MSG_BOTTOM_WAS_LOST;
		return rtr;
	}

	private DisjunctiveAbstractState<STATE> createValidPostOpStateAfterLeaving(final ACTION act,
			final DisjunctiveAbstractState<STATE> preState, final DisjunctiveAbstractState<STATE> preHierState) {

		final DisjunctiveAbstractState<STATE> unifiedPreState = unifyBottom(preState);
		if (unifiedPreState == mBottomState) {
			return unifiedPreState;
		}
		final DisjunctiveAbstractState<STATE> unifiedPreHierState;
		if (preHierState == null) {
			unifiedPreHierState = null;
		} else {
			unifiedPreHierState = unifyBottom(preHierState);
		}

		final DisjunctiveAbstractState<STATE> rtr =
				unifiedPreState.createValidPostOpStateAfterLeaving(mVarProvider, act, unifiedPreHierState);

		assert assertBottomRetained(preState, preHierState, rtr, () -> unifiedPreState
				.createValidPostOpStateAfterLeaving(mVarProvider, act, unifiedPreHierState)) : MSG_BOTTOM_WAS_LOST;
		return rtr;
	}

	private DisjunctiveAbstractState<STATE> createValidPostOpStateHierachicalPre(
			final DisjunctiveAbstractState<STATE> preState, final DisjunctiveAbstractState<STATE> preHierState) {

		final DisjunctiveAbstractState<STATE> unifiedPreState = unifyBottom(preState);
		if (unifiedPreState == mBottomState) {
			return unifiedPreState;
		}
		return unifyBottom(preHierState);
	}

	private DisjunctiveAbstractState<STATE> reducePreState(final DisjunctiveAbstractState<STATE> validPreState,
			final DisjunctiveAbstractState<STATE> succ, final ACTION action) {
		if (!REDUCE_STATES) {
			return validPreState;
		}
		final Set<IProgramVarOrConst> requiredVars = new HashSet<>();
		requiredVars.addAll(getVars(action));
		requiredVars.addAll(succ.getVariables());
		requiredVars.addAll(getMissingOldVars(requiredVars));

		final Set<IProgramVarOrConst> preVars = validPreState.getVariables();
		final Set<IProgramVarOrConst> toRemove = DataStructureUtils.difference(preVars, requiredVars);

		if (mLogger.isDebugEnabled()) {
			mLogger.debug(String.format("Removing %s of %s vars", toRemove.size(), preVars.size()));
			mLogger.debug(String.format("Removing %s", toRemove));
		}

		return validPreState.removeVariables(toRemove);
	}

	private static Set<IProgramVarOrConst> getMissingOldVars(final Set<IProgramVarOrConst> requiredVars) {
		final Set<IProgramVarOrConst> missingOldVars = new HashSet<>();
		for (final IProgramVarOrConst requiredVar : requiredVars) {
			if (requiredVar.isGlobal()) {
				if (requiredVar instanceof IProgramNonOldVar) {
					missingOldVars.add(((IProgramNonOldVar) requiredVar).getOldVar());
				} else if (requiredVar instanceof IProgramOldVar) {
					missingOldVars.add(((IProgramOldVar) requiredVar).getNonOldVar());
				}
			}
		}
		return missingOldVars;
	}

	private DisjunctiveAbstractState<STATE> createValidPostOpStateBeforeLeaving(final ACTION act,
			final DisjunctiveAbstractState<STATE> preState) {

		final DisjunctiveAbstractState<STATE> unifiedPreState = unifyBottom(preState);
		if (unifiedPreState == mBottomState) {
			return unifiedPreState;
		}
		final DisjunctiveAbstractState<STATE> rtr =
				unifiedPreState.createValidPostOpStateBeforeLeaving(mVarProvider, act);

		assert assertBottomRetained(preState, null, rtr,
				() -> unifiedPreState.createValidPostOpStateBeforeLeaving(mVarProvider, act)) : MSG_BOTTOM_WAS_LOST;
		return rtr;
	}

	private DisjunctiveAbstractState<STATE> unifyBottom(final DisjunctiveAbstractState<STATE> state) {
		if (state.isBottom()) {
			return mBottomState;
		}
		return state;
	}

	private IPredicate createPredicateFromState(final DisjunctiveAbstractState<STATE> preState) {
		return mPredicateUnifier.getPredicateFactory().newPredicate(preState.getTerm(mManagedScript.getScript()));
	}

	private boolean assertBottomRetained(final DisjunctiveAbstractState<STATE> pre,
			final DisjunctiveAbstractState<STATE> preHierState, final DisjunctiveAbstractState<STATE> synchronizedState,
			final IFunPointer funReplay) {
		final boolean rtr =
				(!pre.isBottom() && (preHierState == null || !preHierState.isBottom())) || synchronizedState.isBottom();
		if (!rtr) {
			funReplay.run();
		}
		return rtr;
	}

	private boolean assertValidity(final DisjunctiveAbstractState<STATE> preState,
			final DisjunctiveAbstractState<STATE> validPreLinState, final ACTION transition,
			final DisjunctiveAbstractState<STATE> succ, final Validity result) {

		final IPredicate precond = createPredicateFromState(preState);
		final IPredicate postcond = createPredicateFromState(succ);
		final IPredicate precondHier;
		if (validPreLinState == null) {
			precondHier = null;
		} else {
			precondHier = createPredicateFromState(validPreLinState);
		}
		final Validity checkedResult;
		mHtcSmt.releaseLock();
		final DebuggingHoareTripleChecker checkHtc =
				new DebuggingHoareTripleChecker(mServices, mLogger, mCsToolkit, result);
		if (transition instanceof ICallAction) {
			checkedResult = checkHtc.checkCall(precond, (ICallAction) transition, postcond);
		} else if (transition instanceof IReturnAction) {
			checkedResult = checkHtc.checkReturn(precond, precondHier, (IReturnAction) transition, postcond);
		} else {
			checkedResult = checkHtc.checkInternal(precond, (IInternalAction) transition, postcond);
		}
		checkHtc.releaseLock();

		if (checkHtc.isLastOk()) {
			mLogger.debug("HTC assert ok");
			return true;
		}
		if (result == Validity.INVALID && checkedResult == Validity.VALID) {
			mLogger.warn("Rejecting Hoare triple although it is actually valid (Domain " + mDomain.domainDescription()
					+ ")");
			return ACCEPT_REJECTION_DUE_TO_IMPRECISION;
		}

		final Consumer<Object> log;
		if (result == Validity.UNKNOWN) {
			log = mLogger::warn;
		} else {
			log = mLogger::fatal;
		}

		log.accept("--");
		log.accept("Abstract states");
		if (precondHier == null) {
			log.accept("PreS: {" + preState + "}");
		} else {
			log.accept(getMsgPreBefore(preState));
			log.accept(getMsgPreAfter(validPreLinState));
		}
		log.accept(IcfgUtils.getTransformula(transition).getClosedFormula() + " (" + transition + ")");
		log.accept(getMsgPost(succ));
		log.accept("--");

		return result == Validity.UNKNOWN;
	}

	private static String getMsgPreBefore(final Object preState) {
		return "PreBefore: {" + preState + "}";
	}

	private static String getMsgPreAfter(final Object validPreLinState) {
		return "PreAfter: {" + validPreLinState + "}";
	}

	private static String getMsgPost(final Object succ) {
		return "Post: {" + succ + "}";
	}

	private boolean assertIsSubsetOf(final DisjunctiveAbstractState<STATE> leftState,
			final DisjunctiveAbstractState<STATE> rightState, final SubsetResult subResult) {
		final Script script = mManagedScript.getScript();
		mHtcSmt.releaseLock();

		script.echo(new QuotedObject("Start isSubsetOf assertion"));
		final Term left = leftState.getTerm(script);
		final Term right = rightState.getTerm(script);

		final LBool result;
		final LBool expected;
		final Term checkedTerm;
		if (subResult == SubsetResult.EQUAL) {
			checkedTerm = script.term("distinct", left, right);
			expected = LBool.UNSAT;
		} else {
			final Term baseTerm = script.term("=>", left, right);
			if (baseTerm.getFreeVars().length > 0) {
				checkedTerm = script.quantifier(QuantifiedFormula.FORALL, baseTerm.getFreeVars(), baseTerm);
			} else {
				checkedTerm = baseTerm;
			}
			expected = subResult == SubsetResult.NONE ? LBool.UNSAT : LBool.SAT;
		}
		result = SmtUtils.checkSatTerm(script, checkedTerm);

		if (result == LBool.UNKNOWN || result == expected) {
			script.echo(buildQuoteEndIsSubsetOf());
			return true;
		}
		if (subResult == SubsetResult.NONE) {
			script.echo(buildQuoteEndIsSubsetOf());
			return true;
		}

		final Term leftSimpl = SmtUtils.simplify(mManagedScript, left, mServices, SimplificationTechnique.SIMPLIFY_DDA);
		final Term rightSimpl =
				SmtUtils.simplify(mManagedScript, right, mServices, SimplificationTechnique.SIMPLIFY_DDA);
		final Term checkSimpl =
				SmtUtils.simplify(mManagedScript, checkedTerm, mServices, SimplificationTechnique.SIMPLIFY_DDA);

		mLogger.fatal("isSubsetOf assertion failed");
		mLogger.fatal("Checking left isSubsetOrEqual right = " + subResult);
		mLogger.fatal("leftState  : " + leftState.toLogString());
		mLogger.fatal("rightState : " + rightState.toLogString());
		mLogger.fatal("left       : " + left.toStringDirect());
		mLogger.fatal("right      : " + right.toStringDirect());
		mLogger.fatal("leftSim    : " + leftSimpl.toStringDirect());
		mLogger.fatal("rightSim   : " + rightSimpl.toStringDirect());
		mLogger.fatal("checking   : " + checkedTerm.toStringDirect());
		mLogger.fatal("checkingSim: " + checkSimpl.toStringDirect());
		mLogger.fatal("Result is " + result + " and should be " + expected);
		mLogger.fatal("Solver was " + script.getInfo(":name") + " in version " + script.getInfo(":version"));

		final SubsetResult reComputeForDebug = leftState.isSubsetOf(rightState);
		mLogger.fatal(reComputeForDebug);
		script.echo(buildQuoteEndIsSubsetOf());
		return false;
	}

	private static QuotedObject buildQuoteEndIsSubsetOf() {
		return new QuotedObject("End isSubsetOf assertion");
	}

	@FunctionalInterface
	private static interface IFunPointer {
		void run();
	}

}
