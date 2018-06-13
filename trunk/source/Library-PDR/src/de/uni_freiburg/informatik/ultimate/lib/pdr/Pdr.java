/*
 * Copyright (C) 2018 Jonas Werner (jonaswerner95@gmail.com)
 * Copyright (C) 2018 University of Freiburg
 *
 * This file is part of the ULTIMATE PDR library .
 *
 * The ULTIMATE IcfgTransformer is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE IcfgTransformer is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE PDR library . If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE PDR library , or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE PDR library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.pdr;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.ToolchainCanceledException;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.translation.IProgramExecution;
import de.uni_freiburg.informatik.ultimate.lib.pdr.PdrBenchmark.PdrStatisticsDefinitions;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.IcfgUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.ICallAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgCallTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgInternalTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgReturnTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IInternalAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IReturnAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgCallTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocationIterator;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgReturnTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hoaretriple.IHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hoaretriple.IHoareTripleChecker.Validity;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.PartialQuantifierElimination;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.interpolant.IInterpolantGenerator;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.interpolant.InterpolantComputationStatus;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.interpolant.InterpolantComputationStatus.ItpErrorStatus;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.PredicateTransformer;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.TermDomainOperationProvider;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.tracecheck.ITraceCheck;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.tracecheck.ITraceCheckPreferences;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.tracecheck.TraceCheckReasonUnknown;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.tracecheck.TraceCheckReasonUnknown.ExceptionHandlingCategory;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.tracecheck.TraceCheckReasonUnknown.Reason;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.PathProgram;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.PathProgram.PathProgramConstructionResult;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Triple;
import de.uni_freiburg.informatik.ultimate.util.statistics.IStatisticsDataProvider;

/**
 *
 * @author Jonas Werner (jonaswerner95@gmail.com)
 *
 */
public class Pdr<LETTER extends IIcfgTransition<?>> implements ITraceCheck, IInterpolantGenerator<LETTER> {

	private final ILogger mLogger;
	private final IUltimateServiceProvider mServices;
	private final Map<IcfgLocation, List<Pair<changedFrame, IPredicate>>> mFrames;
	private final ManagedScript mScript;
	private final PredicateTransformer<Term, IPredicate, TransFormula> mPredTrans;
	private final IIcfg<? extends IcfgLocation> mIcfg;
	private final IIcfg<? extends IcfgLocation> mPpIcfg;
	private final CfgSmtToolkit mCsToolkit;
	private final IHoareTripleChecker mHtc;
	private final IPredicateUnifier mPredicateUnifier;
	private final IPredicate mTruePred;
	private final IPredicate mFalsePred;
	private final List<LETTER> mTrace;
	private final PdrBenchmark mPdrBenchmark;

	private boolean mTraceCheckFinishedNormally;
	private IProgramExecution<IcfgEdge, Term> mFeasibleProgramExecution;
	private ToolchainCanceledException mToolchainCanceledException;
	private LBool mIsTraceCorrect;
	private IPredicate[] mInterpolants;
	private TraceCheckReasonUnknown mReasonUnknown;

	/**
	 * To indicate whether a frame has been changed. It is possible to add "true" to frames, but that was ignored in the
	 * propagation phase.
	 */
	private enum changedFrame {
		CHANGED, UNCHANGED
	}

	public Pdr(final ILogger logger, final ITraceCheckPreferences prefs, final IPredicateUnifier predicateUnifier,
			final IHoareTripleChecker htc, final List<LETTER> counterexample) {
		// from params
		mLogger = logger;
		mPredicateUnifier = predicateUnifier;
		mHtc = htc;
		mTrace = counterexample;

		// stuff from prefs
		mServices = prefs.getUltimateServices();
		mIcfg = prefs.getIcfgContainer();

		// stuff initialized here
		mPdrBenchmark = new PdrBenchmark();

		mFrames = new HashMap<>();
		final PathProgramConstructionResult pp =
				PathProgram.constructPathProgram("errorPP", mIcfg, new HashSet<>(counterexample));

		mPpIcfg = pp.getPathProgram();
		mCsToolkit = mPpIcfg.getCfgSmtToolkit();
		mScript = mCsToolkit.getManagedScript();
		mPredTrans = new PredicateTransformer<>(mScript, new TermDomainOperationProvider(mServices, mScript));

		mTruePred = mPredicateUnifier.getOrConstructPredicate(mScript.getScript().term("true"));
		mFalsePred = mPredicateUnifier.getOrConstructPredicate(mScript.getScript().term("false"));

		mLogger.debug("PDR initialized...");

		try {
			mPdrBenchmark.start(PdrStatisticsDefinitions.PDR_RUNTIME);
			mIsTraceCorrect = computePdr();
			mTraceCheckFinishedNormally = true;
			mReasonUnknown = null;
		} catch (final ToolchainCanceledException tce) {
			mToolchainCanceledException = tce;
			mTraceCheckFinishedNormally = false;
			mReasonUnknown = new TraceCheckReasonUnknown(Reason.ULTIMATE_TIMEOUT, tce,
					ExceptionHandlingCategory.KNOWN_DEPENDING);
		} catch (final SMTLIBException e) {
			mTraceCheckFinishedNormally = false;
			mReasonUnknown = TraceCheckReasonUnknown.constructReasonUnknown(e);
		} finally {
			mPdrBenchmark.stop(PdrStatisticsDefinitions.PDR_RUNTIME);
		}
	}

	private LBool computePdr() {

		final Set<? extends IcfgLocation> init = mPpIcfg.getInitialNodes();
		final Set<? extends IcfgLocation> error = IcfgUtils.getErrorLocations(mPpIcfg);

		/**
		 * Check for 0-Counter-Example
		 */
		for (final IcfgLocation initNode : init) {
			if (error.contains(initNode)) {
				mLogger.debug("Error is reachable.");
				return LBool.SAT;
			}
		}

		/**
		 * Initialize level 0.
		 */
		final IcfgLocationIterator<? extends IcfgLocation> iter = new IcfgLocationIterator<>(mPpIcfg);
		while (iter.hasNext()) {
			final IcfgLocation loc = iter.next();
			if (error.contains(loc)) {
				continue;
			}
			mFrames.put(loc, new ArrayList<>());
			if (init.contains(loc)) {
				mFrames.get(loc).add(new Pair<changedFrame, IPredicate>(changedFrame.UNCHANGED, mTruePred));
			} else {
				mFrames.get(loc).add(new Pair<changedFrame, IPredicate>(changedFrame.UNCHANGED, mFalsePred));
			}
		}

		int level = 0;

		while (true) {
			if (!mServices.getProgressMonitorService().continueProcessing()) {
				throw new ToolchainCanceledException(getClass(), "Timeout or canceled while running Pdr");
			}
			/**
			 * Initialize new level.
			 */
			for (final Entry<IcfgLocation, List<Pair<changedFrame, IPredicate>>> trace : mFrames.entrySet()) {
				trace.getValue().add(new Pair<changedFrame, IPredicate>(changedFrame.UNCHANGED, mTruePred));
			}

			level += 1;

			final List<Triple<IPredicate, IcfgLocation, Integer>> proofObligations = new ArrayList<>();

			/**
			 * Generate the initial proof-obligations
			 */
			for (final IcfgEdge edge : error.iterator().next().getIncomingEdges()) {

				final Term sp = mPredTrans.strongestPostcondition(mTruePred, edge.getTransformula());
				final IPredicate proofObligationPred = mPredicateUnifier.getOrConstructPredicate(sp);
				final Triple<IPredicate, IcfgLocation, Integer> initialProofObligation =
						new Triple<>(proofObligationPred, edge.getSource(), level);
				proofObligations.add(initialProofObligation);
			}

			mLogger.debug("Initial POs: " + proofObligations);

			/**
			 * Generated proof-obligation on level 0 -> error is reachable
			 */
			if (!blockingPhase(proofObligations)) {
				// throw new UnsupportedOperationException("error reachable");
				if (mLogger.isDebugEnabled()) {
					mLogger.debug(
							"Error trace found. Frames: " + mFrames.entrySet().stream()
									.map(a -> a.getKey().getDebugIdentifier() + ": {"
											+ a.getValue().stream().map(Pair<changedFrame, IPredicate>::toString)
													.collect(Collectors.joining(","))
											+ "}")
									.collect(Collectors.joining(",")));
				}
				mLogger.debug("Error is reachable.");
				return LBool.SAT;
			}

			/**
			 * Found invariant -> error is not reachable
			 */
			if (propagationPhase()) {
				// throw new UnsupportedOperationException("error not
				// reachable");
				if (mLogger.isDebugEnabled()) {
					mLogger.debug(
							"Error trace found. Frames: " + mFrames.entrySet().stream()
									.map(a -> a.getKey().getDebugIdentifier() + ": {"
											+ a.getValue().stream().map(Pair<changedFrame, IPredicate>::toString)
													.collect(Collectors.joining(","))
											+ "}")
									.collect(Collectors.joining(",")));
				}
				mLogger.debug("Error is not reachable.");
				mInterpolants = computeInterpolants();
				return LBool.UNSAT;
			}
		}
	}

	/**
	 * Blocking-phase, for blocking proof-obligations.
	 *
	 * @return false, if proof-obligation on level 0 is created true, if there is no proof-obligation left
	 */
	private boolean blockingPhase(final List<Triple<IPredicate, IcfgLocation, Integer>> initialProofObligations) {

		mLogger.debug("Begin Blocking Phase: \n");

		final Deque<Triple<IPredicate, IcfgLocation, Integer>> proofObligations =
				new ArrayDeque<>(initialProofObligations);
		while (!proofObligations.isEmpty()) {
			final Triple<IPredicate, IcfgLocation, Integer> proofObligation = proofObligations.pop();
			final IPredicate toBeBlocked = proofObligation.getFirst();
			final IcfgLocation location = proofObligation.getSecond();
			final int level = proofObligation.getThird();

			mLogger.debug("predecessors: " + location.getIncomingEdges());
			for (final IcfgEdge predecessorTransition : location.getIncomingEdges()) {
				mLogger.debug("Predecessor Transition: " + predecessorTransition);
				final IcfgLocation predecessor = predecessorTransition.getSource();
				final IPredicate predecessorFrame = mFrames.get(predecessor).get(level - 1).getSecond();

				/**
				 * @TODO error on other actions that are not IInternalAction
				 */

				final Validity result = checkSatInternal(predecessorFrame, predecessorTransition, toBeBlocked);

				/**
				 * If Sat generate new proof-obligation
				 */
				if (result == Validity.INVALID) {
					/**
					 * Found Error trace
					 */
					if (level - 1 == 0) {
						return false;
					}

					final IPredicate preCondition;

					if (predecessorTransition instanceof IIcfgInternalTransition) {
						final Term pre = mPredTrans.pre(toBeBlocked, predecessorTransition.getTransformula());
						preCondition = mPredicateUnifier.getOrConstructPredicate(pre);
						if (mLogger.isDebugEnabled()) {
							mLogger.debug(String.format("pre(%s, %s) == %s", toBeBlocked, predecessorTransition, pre));
						}

					} else if (predecessorTransition instanceof IIcfgCallTransition) {
						final TransFormula globalVarsAssignments = mCsToolkit.getOldVarsAssignmentCache()
								.getGlobalVarsAssignment(predecessorTransition.getSucceedingProcedure());
						final TransFormula oldVarAssignments = mCsToolkit.getOldVarsAssignmentCache()
								.getOldVarsAssignment(predecessorTransition.getSucceedingProcedure());
						final Set<IProgramNonOldVar> modifiableGlobals = mCsToolkit.getModifiableGlobalsTable()
								.getModifiedBoogieVars(predecessorTransition.getSucceedingProcedure());
						preCondition =
								(IPredicate) mPredTrans.preCall(toBeBlocked, predecessorTransition.getTransformula(),
										globalVarsAssignments, oldVarAssignments, modifiableGlobals);

					} else if (predecessorTransition instanceof IIcfgReturnTransition) {
						/*
						 * What to do here?
						 */
						throw new UnsupportedOperationException();

					} else {
						throw new UnsupportedOperationException(
								"Unknown transition type: " + predecessorTransition.getClass().toString());
					}

					final Triple<IPredicate, IcfgLocation, Integer> newProofObligation =
							new Triple<>(preCondition, predecessor, level - 1);

					// proofObligations.addFirst(proofObligation);
					proofObligations.addFirst(newProofObligation);
					if (mLogger.isDebugEnabled()) {
						mLogger.debug("New PO: " + newProofObligation);
					}

					/**
					 * If Unsat strengthen the frames of the location
					 */
				} else if (result == Validity.VALID) {
					for (int i = 0; i <= level; i++) {
						IPredicate fTerm = mFrames.get(location).get(i).getSecond();
						final IPredicate negToBeBlocked = mPredicateUnifier.getPredicateFactory().not(toBeBlocked);
						fTerm = mPredicateUnifier.getPredicateFactory().and(fTerm, negToBeBlocked);
						fTerm = mPredicateUnifier.getOrConstructPredicate(fTerm);
						mFrames.get(location).set(i, new Pair<changedFrame, IPredicate>(changedFrame.CHANGED, fTerm));
					}

				} else {
					// mIsTraceCorrect = LBool.UNKNOWN;
					throw new UnsupportedOperationException("what to do with unknown?");
				}
			}
		}
		return true;
	}

	/**
	 * Propagation-Phase, for finding invariants
	 */
	private boolean propagationPhase() {
		mLogger.debug("Begin Propagation Phase: \n");
		for (final Entry<IcfgLocation, List<Pair<changedFrame, IPredicate>>> locationTrace : mFrames.entrySet()) {
			final List<Pair<changedFrame, IPredicate>> frames = locationTrace.getValue();

			for (int i = 0; i < frames.size(); i++) {
				final IPredicate p1 = frames.get(i).getSecond();
				if (frames.get(i).getFirst() == changedFrame.UNCHANGED) {
					continue;
				}
				for (int k = i + 1; k < frames.size(); k++) {
					if (frames.get(k).getFirst() == changedFrame.UNCHANGED) {
						continue;
					}
					final IPredicate p2 = frames.get(k).getSecond();
					if (p1.getFormula().equals(p2.getFormula())) {
						mLogger.debug("Invariant Found: " + frames.get(i) + " equals " + frames.get(k));
						return true;
					}
				}
			}
		}
		return false;
	}

	/**
	 * Use a {@link IHoareTripleChecker} to check for satisfiability of pre &and; tf &and; post
	 *
	 * This method converts the post condition because an {@link IHoareTripleChecker} checks for P &and; S &and; !Q
	 *
	 * @param pre
	 * @param trans
	 * @param post
	 *
	 * @return {@link Validity#VALID} iff the formula is unsat, {@link Validity#INVALID} iff the formula is sat,
	 *         {@link Validity#UNKNOWN} iff the solver was not able to find a solution, and {@link Validity#NOT_CHECKED}
	 *         should not be returned
	 */
	private Validity checkSatInternal(final IPredicate pre, final IAction trans, final IPredicate post) {
		final IPredicate notP = not(post);
		Validity result = Validity.NOT_CHECKED;

		if (trans instanceof IIcfgInternalTransition) {
			result = mHtc.checkInternal(pre, (IInternalAction) trans, notP);
		} else if (trans instanceof IcfgCallTransition) {
			result = mHtc.checkCall(pre, (ICallAction) trans, notP);
		} else if (trans instanceof IcfgReturnTransition) {
			/*
			 * @TODO how does this work?
			 */
			result = mHtc.checkReturn(mTruePred, pre, (IReturnAction) trans, notP);
		}

		if (mLogger.isDebugEnabled()) {
			mLogger.debug(String.format(" %s && %s && %s is %s", pre, trans, post,
					(result == Validity.VALID ? "unsat" : (result == Validity.INVALID ? "sat" : "unknown"))));
		}
		assert result != Validity.NOT_CHECKED;
		return result;

	}

	private IPredicate not(final IPredicate pred) {
		return mPredicateUnifier.getOrConstructPredicate(mPredicateUnifier.getPredicateFactory().not(pred));
	}

	/**
	 * Compute interpolants of mTrace.
	 * 
	 * @ToDo optimization
	 * @return
	 */
	private IPredicate[] computeInterpolants() {
		/*
		 * What do with live variables? How does unsatcore work?
		 */
		mLogger.debug("computing interpolants.");

		Term traceTerm = mScript.getScript().term("true");
		final Iterator<LETTER> traceIt = mTrace.iterator();
		while (traceIt.hasNext()) {
			final LETTER l = traceIt.next();
			traceTerm = mScript.getScript().term("and", traceTerm, l.getTransformula().getFormula());
		}

		// always sat? why?
		final LBool sat = mScript.getScript().checkSat();
		if (sat == LBool.UNSAT) {
			final Term[] unsatCore = mScript.getScript().getUnsatCore();
		}

		final IPredicate[] interpolants = new IPredicate[mTrace.size()];

		interpolants[0] = mTruePred;
		for (int i = 1; i < mTrace.size(); i++) {
			final Term interpolantTerm =
					mPredTrans.strongestPostcondition(interpolants[i - 1], mTrace.get(i - 1).getTransformula());
			interpolants[i] = mPredicateUnifier.getOrConstructPredicate(interpolantTerm);
		}
		return Arrays.copyOfRange(interpolants, 1, mTrace.size());
	}

	private IProgramExecution<IcfgEdge, Term> computeProgramExecution() {
		// TODO: construct a real IProgramExecution using IcfgProgramExecutionBuilder (DD needs to refactor s.t. the
		// class becomes available here).
		if (mIsTraceCorrect == LBool.SAT) {
			return IProgramExecution.emptyExecution(Term.class, IcfgEdge.class);
		}
		return null;
	}

	/** ITraceCheck interface **/

	@Override
	public LBool isCorrect() {
		return mIsTraceCorrect;
	}

	@Override
	public IPredicate getPrecondition() {
		return mTruePred;
	}

	@Override
	public IPredicate getPostcondition() {
		return mFalsePred;
	}

	@Override
	public Map<Integer, IPredicate> getPendingContexts() {
		return Collections.emptyMap();
	}

	@Override
	public boolean providesRcfgProgramExecution() {
		return mIsTraceCorrect != LBool.SAT;
	}

	@Override
	public IProgramExecution<IcfgEdge, Term> getRcfgProgramExecution() {
		if (mFeasibleProgramExecution == null) {
			mFeasibleProgramExecution = computeProgramExecution();
		}
		return mFeasibleProgramExecution;
	}

	@Override
	public IStatisticsDataProvider getTraceCheckBenchmark() {
		return mPdrBenchmark;
	}

	@Override
	public ToolchainCanceledException getToolchainCanceledExpection() {
		return mToolchainCanceledException;
	}

	@Override
	public TraceCheckReasonUnknown getTraceCheckReasonUnknown() {
		return mReasonUnknown;
	}

	@Override
	public boolean wasTracecheckFinishedNormally() {
		return mTraceCheckFinishedNormally;
	}

	/** End ITraceCheck interface **/

	/** IInterpolantGenerator interface **/

	@Override
	public List<LETTER> getTrace() {
		return mTrace;
	}

	@Override
	public IPredicate[] getInterpolants() {
		return mInterpolants;
	}

	@Override
	public IPredicateUnifier getPredicateUnifier() {
		return mPredicateUnifier;
	}

	@Override
	public boolean isPerfectSequence() {
		// if we analyze path programs, each of our sequences is correct
		return isCorrect() == LBool.UNSAT;
	}

	@Override
	public InterpolantComputationStatus getInterpolantComputationStatus() {
		if (isCorrect() == LBool.UNSAT) {
			return new InterpolantComputationStatus(true, null, null);
		} else if (isCorrect() == LBool.SAT) {
			return new InterpolantComputationStatus(false, ItpErrorStatus.TRACE_FEASIBLE, null);
		} else {
			throw new UnsupportedOperationException();
		}
	}

	/** End IInterpolantGenerator interface **/

}
