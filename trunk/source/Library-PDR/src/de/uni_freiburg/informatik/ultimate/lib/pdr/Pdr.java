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
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.IIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.IcfgUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.ModifiableGlobalsTable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.ICallAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgCallTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgInternalTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgReturnTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IInternalAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IReturnAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocationIterator;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.TransFormulaUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramOldVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hoaretriple.IHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hoaretriple.IHoareTripleChecker.Validity;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.PartialQuantifierElimination;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.Substitution;
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

	/**
	 * To indicate whether a frame has been changed. It is possible to add "true" to frames, but that was ignored in the
	 * propagation phase.
	 */
	private enum ChangedFrame {
		CHANGED, UNCHANGED
	}

	/**
	 * How to deal with procedures.
	 *
	 * @author Jonas Werner
	 *
	 */
	private enum DealWithProcedures {
		THROW_EXCEPTION, CONTINUE
	}

	private static final boolean USE_INTERPOLATION = false;

	/**
	 * Currently we cannot handle procedures.
	 */
	private final DealWithProcedures mDealWithProcedures = DealWithProcedures.THROW_EXCEPTION;

	private final ILogger mLogger;
	private final IUltimateServiceProvider mServices;
	private final Map<IcfgLocation, List<Pair<ChangedFrame, IPredicate>>> mFrames;
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
	private final IIcfgSymbolTable mSymbolTable;
	private final IPredicate mAxioms;
	private final Deque<ProofObligation> mProofObligations;

	private boolean mTraceCheckFinishedNormally;
	private IProgramExecution<IIcfgTransition<IcfgLocation>, Term> mFeasibleProgramExecution;
	private ToolchainCanceledException mToolchainCanceledException;
	private LBool mIsTraceCorrect;
	private IPredicate[] mInterpolants;
	private TraceCheckReasonUnknown mReasonUnknown;
	private int mInvarSpot;
	private int mLevel;

	public Pdr(final ILogger logger, final ITraceCheckPreferences prefs, final IPredicateUnifier predicateUnifier,
			final IHoareTripleChecker htc, final List<LETTER> counterexample) {
		// from params
		mLogger = logger;
		mPredicateUnifier = predicateUnifier;
		mHtc = htc;
		mTrace = counterexample;

		mProofObligations = new ArrayDeque<>();

		mInvarSpot = -1;
		mLevel = 0;

		// stuff from prefs
		mServices = prefs.getUltimateServices();
		mIcfg = prefs.getIcfgContainer();

		mSymbolTable = mIcfg.getCfgSmtToolkit().getSymbolTable();

		// stuff initialized here
		mPdrBenchmark = new PdrBenchmark();

		mFrames = new HashMap<>();
		final PathProgramConstructionResult pp =
				PathProgram.constructPathProgram("errorPP", mIcfg, new HashSet<>(counterexample));

		mPpIcfg = pp.getPathProgram();
		mCsToolkit = mPpIcfg.getCfgSmtToolkit();
		mScript = mCsToolkit.getManagedScript();
		mPredTrans = new PredicateTransformer<>(mScript, new TermDomainOperationProvider(mServices, mScript));
		mAxioms = mPredicateUnifier.getOrConstructPredicate(mCsToolkit.getSmtSymbols().getAxioms());

		mTruePred = mPredicateUnifier.getOrConstructPredicate(mScript.getScript().term("true"));
		mFalsePred = mPredicateUnifier.getOrConstructPredicate(mScript.getScript().term("false"));

		mLogger.info("Analyzing path program with PDR");

		try {
			mPdrBenchmark.start(PdrStatisticsDefinitions.PDR_RUNTIME);
			mIsTraceCorrect = computePdr();
			mLogger.info("Finished analyzing path program with PDR");
			mTraceCheckFinishedNormally = true;
			mReasonUnknown = null;
		} catch (final ToolchainCanceledException tce) {
			mTraceCheckFinishedNormally = false;
			mIsTraceCorrect = LBool.UNKNOWN;
			mToolchainCanceledException = tce;
			mReasonUnknown = new TraceCheckReasonUnknown(Reason.ULTIMATE_TIMEOUT, tce,
					ExceptionHandlingCategory.KNOWN_DEPENDING);
		} catch (final SMTLIBException e) {
			mTraceCheckFinishedNormally = false;
			mIsTraceCorrect = LBool.UNKNOWN;
			mReasonUnknown = TraceCheckReasonUnknown.constructReasonUnknown(e);
		} finally {
			mPdrBenchmark.stop(PdrStatisticsDefinitions.PDR_RUNTIME);
		}
	}

	private LBool computePdr() {

		final Set<? extends IcfgLocation> init = mPpIcfg.getInitialNodes();
		final Set<? extends IcfgLocation> error = IcfgUtils.getErrorLocations(mPpIcfg);

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
				mFrames.get(loc).add(new Pair<>(ChangedFrame.UNCHANGED, mAxioms));
			} else {
				mFrames.get(loc).add(new Pair<>(ChangedFrame.UNCHANGED, mFalsePred));
			}
		}

		/**
		 * Check for 0-Counter-Example
		 */
		for (final IcfgLocation initNode : init) {
			if (error.contains(initNode)) {
				mLogger.debug("Error is reachable.");
				return LBool.SAT;
			}
			for (final IcfgEdge loc : initNode.getOutgoingEdges()) {
				if (error.contains(loc.getTarget())) {
					if (mAxioms != null) {
						final Validity result = checkSatInternal(mTruePred, (IInternalAction) loc, mAxioms);
						if (IHoareTripleChecker.convertValidity2Lbool(result) == LBool.UNSAT) {
							mInvarSpot = 0;
							mInterpolants = computeInterpolants();
							return LBool.UNSAT;
						}
					}
					return LBool.SAT;
				}
			}
		}

		/**
		 * Generate the initial proof-obligations
		 */
		for (final IcfgEdge edge : error.iterator().next().getIncomingEdges()) {
			final Term sp = mPredTrans.pre(mTruePred, edge.getTransformula());
			final IPredicate proofObligationPred = mPredicateUnifier.getPredicateFactory().newPredicate(sp);
			final ProofObligation initialProofObligation =
					new ProofObligation(proofObligationPred, edge.getSource(), mLevel);

			mProofObligations.add(initialProofObligation);
		}

		while (true) {
			if (!mServices.getProgressMonitorService().continueProcessing()) {
				throw new ToolchainCanceledException(getClass(), "Timeout or canceled while running Pdr");
			}
			/**
			 * Initialize new level.
			 */
			for (final Entry<IcfgLocation, List<Pair<ChangedFrame, IPredicate>>> trace : mFrames.entrySet()) {
				trace.getValue().add(new Pair<>(ChangedFrame.UNCHANGED, mAxioms));
			}

			mLevel += 1;

			/**
			 * Generated proof-obligation on level 0 -> error reachable
			 */
			if (!blockingPhase()) {
				if (mLogger.isDebugEnabled()) {
					mLogger.debug(
							"Error trace found. Frames: " + mFrames.entrySet().stream()
									.map(a -> a.getKey().getDebugIdentifier() + ": {"
											+ a.getValue().stream().map(Pair<ChangedFrame, IPredicate>::toString)
													.collect(Collectors.joining(","))
											+ "}")
									.collect(Collectors.joining(",")));
				}
				mLogger.debug("Error is reachable.");
				return LBool.SAT;
			}

			/**
			 * Found a global fixpoint position -> error not reachable
			 */
			if (propagationPhase()) {
				if (mLogger.isDebugEnabled()) {
					mLogger.debug("Frames:");
					for (final Entry<IcfgLocation, List<Pair<ChangedFrame, IPredicate>>> entry : mFrames.entrySet()) {
						mLogger.debug("  " + entry.getKey().getDebugIdentifier() + ": " + entry.getValue().stream()
								.map(Pair<ChangedFrame, IPredicate>::toString).collect(Collectors.joining(",")));
					}
					mLogger.debug("PP:");
					mLogger.debug("  " + new IcfgLocationIterator<>(mPpIcfg).asStream()
							.map(a -> a.getDebugIdentifier().toString()).collect(Collectors.joining(",")));
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
	private final boolean blockingPhase() {

		mLogger.debug("Begin Blocking Phase: on Level: " + mLevel);

		final Deque<ProofObligation> proofObligations = new ArrayDeque<>(mProofObligations);
		while (!proofObligations.isEmpty()) {
			final ProofObligation proofObligation = proofObligations.pop();
			final IPredicate toBeBlocked = proofObligation.getToBeBlocked();
			final IcfgLocation location = proofObligation.getLocation();
			final int level = mLevel - proofObligation.getLevel();

			if (mLogger.isDebugEnabled()) {
				mLogger.debug("ProofObligation: " + proofObligation);
				mLogger.debug("predecessors: " + location.getIncomingNodes());
			}
			for (final IcfgEdge predecessorTransition : location.getIncomingEdges()) {
				if (mLogger.isDebugEnabled()) {
					mLogger.debug("Predecessor Transition: " + predecessorTransition);
				}
				final IcfgLocation predecessor = predecessorTransition.getSource();
				final IPredicate predecessorFrame = mFrames.get(predecessor).get(level - 1).getSecond();
				final Triple<IPredicate, IAction, IPredicate> query =
						new Triple<>(predecessorFrame, predecessorTransition, toBeBlocked);

				/*
				 * Check whether the proofobligation has already been blocked to skip the rest.
				 */
				if (proofObligation.getBlockedQueries().contains(query)) {
					mLogger.debug("Query already blocked.");
					updateFrames(toBeBlocked, location, level);
					continue;
				}

				final Validity result;

				/*
				 * Dealing with internal transitions:
				 */
				if (predecessorTransition instanceof IIcfgInternalTransition) {
					result = checkSatInternal(query.getFirst(), (IInternalAction) query.getSecond(), query.getThird());
					/*
					 * Query is satisfiable: generate new proofobligation
					 */
					if (result == Validity.INVALID) {
						if (level - 1 == 0) {
							return false;
						}

						Term pre = mPredTrans.pre(query.getThird(), query.getSecond().getTransformula());
						if (pre instanceof QuantifiedFormula) {
							pre = PartialQuantifierElimination.tryToEliminate(mServices, mLogger, mScript, pre,
									SimplificationTechnique.SIMPLIFY_DDA,
									XnfConversionTechnique.BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION);
						}
						final IPredicate prePred = mPredicateUnifier.getOrConstructPredicate(pre);
						addProofObligation(proofObligations, proofObligation, level, predecessor, prePred);

						if (mLogger.isDebugEnabled()) {
							mLogger.debug(
									String.format("pre(%s, %s) == %s", toBeBlocked, predecessorTransition, prePred));
						}

						/*
						 * Query is not satisfiable: strengthen the frames of location.
						 */
					} else if (result == Validity.VALID) {
						if (USE_INTERPOLATION) {
							final IPredicate interpolant =
									getInterpolant((IcfgEdge) query.getSecond(), query.getFirst(), query.getThird());
							if (interpolant != null) {
								// final List<IPredicate> predsForDumbPeople = new ArrayList<>();
								// predsForDumbPeople.add(not(interpolant));
								// predsForDumbPeople.add(mPredicateUnifier.getOrConstructPredicate(query.getThird()));
								updateFrames(interpolant, location, level);
							} else {
								updateFrames(query.getThird(), location, level);
							}
						} else {
							updateFrames(query.getThird(), location, level);
						}
						proofObligation.addBlockedQuery(query);
					} else {
						mLogger.error(String.format("Internal query %s && %s && %s was unknown!", query.getFirst(),
								query.getSecond(), query.getThird()));
						throw new UnsupportedOperationException("Solver returned unknown");
					}

					/*
					 * Dealing with procedure calls TODO:
					 */
				} else if (predecessorTransition instanceof IIcfgCallTransition) {
					if (mDealWithProcedures.equals(DealWithProcedures.THROW_EXCEPTION)) {
						throw new UnsupportedOperationException("Cannot deal with procedures");
					}
					result = checkSatCall(predecessorFrame, (ICallAction) predecessorTransition, toBeBlocked);
					/*
					 * Query is satisfiable: generate new proofobligation
					 */
					if (result == Validity.INVALID) {
						if (level - 1 == 0) {
							return false;
						}
						final TransFormula globalVarsAssignments = mCsToolkit.getOldVarsAssignmentCache()
								.getGlobalVarsAssignment(predecessorTransition.getSucceedingProcedure());
						final TransFormula oldVarAssignments = mCsToolkit.getOldVarsAssignmentCache()
								.getOldVarsAssignment(predecessorTransition.getSucceedingProcedure());
						final Set<IProgramNonOldVar> modifiableGlobals = mCsToolkit.getModifiableGlobalsTable()
								.getModifiedBoogieVars(predecessorTransition.getSucceedingProcedure());
						final Term pre = mPredTrans.preCall(toBeBlocked, predecessorTransition.getTransformula(),
								globalVarsAssignments, oldVarAssignments, modifiableGlobals);
						final IPredicate preCondition = mPredicateUnifier.getOrConstructPredicate(pre);
						addProofObligation(proofObligations, proofObligation, level, predecessor, preCondition);
						/*
						 * Query is not satisfiable: strengthen the frames of location.
						 */
					} else if (result == Validity.VALID) {
						updateFrames(toBeBlocked, location, level);
					} else {
						mLogger.error(String.format("Call query %s && %s && %s was unknown!", query.getFirst(),
								query.getSecond(), query.getThird()));
						throw new UnsupportedOperationException("Solver returned unknown");
					}

					/*
					 * Dealing with procedure returns TODO:
					 */
				} else if (predecessorTransition instanceof IIcfgReturnTransition) {
					if (mDealWithProcedures.equals(DealWithProcedures.THROW_EXCEPTION)) {
						throw new UnsupportedOperationException("Cannot deal with procedures");
					}
					final IIcfgReturnTransition<?, ?> returnTrans = (IIcfgReturnTransition<?, ?>) predecessorTransition;
					final IcfgLocation pp = returnTrans.getCallerProgramPoint();
					final List<Pair<ChangedFrame, IPredicate>> callerFrame = mFrames.get(pp);
					final UnmodifiableTransFormula globalVarsAssignments = mCsToolkit.getOldVarsAssignmentCache()
							.getGlobalVarsAssignment(predecessorTransition.getSucceedingProcedure());
					final UnmodifiableTransFormula oldVarAssignments = mCsToolkit.getOldVarsAssignmentCache()
							.getOldVarsAssignment(predecessorTransition.getSucceedingProcedure());
					final Set<IProgramNonOldVar> modifiableGlobals = mCsToolkit.getModifiableGlobalsTable()
							.getModifiedBoogieVars(predecessorTransition.getSucceedingProcedure());
					final Pair<List<LETTER>, UnmodifiableTransFormula> proc = getProcedureTrace(pp, returnTrans,
							globalVarsAssignments, oldVarAssignments, modifiableGlobals);
					final UnmodifiableTransFormula procFormula = proc.getSecond();
					final IPredicate preHier = mPredicateUnifier
							.getOrConstructPredicate(mPredTrans.pre(callerFrame.get(level).getSecond(), procFormula));
					result = checkSatReturn(predecessorFrame, preHier, returnTrans, toBeBlocked);
					/*
					 * Query is satisfiable: generate new proofobligation
					 */
					if (result == Validity.INVALID) {
						if (level - 1 == 0) {
							return false;
						}
						final Term pre = mPredTrans.preReturn(toBeBlocked, preHier, returnTrans.getAssignmentOfReturn(),
								returnTrans.getLocalVarsAssignmentOfCall(), oldVarAssignments, modifiableGlobals);

						final IPredicate preCondition = mPredicateUnifier.getOrConstructPredicate(pre);
						addProofObligation(proofObligations, proofObligation, level, predecessor, preCondition);
						/*
						 * Query is not satisfiable: strengthen the frames of location.
						 */
					} else if (result == Validity.VALID) {
						updateFrames(toBeBlocked, location, level);
					} else {
						mLogger.error(String.format("Return query %s && %s && %s && %s was unknown", predecessorFrame,
								preHier, returnTrans, toBeBlocked));
						throw new UnsupportedOperationException("Solver returned unknown");
					}
				} else {
					throw new UnsupportedOperationException(
							"Unknown transition type: " + predecessorTransition.getClass().toString());
				}
			}
		}
		return true;

	}

	/**
	 * Compute Interpolant of unsatisfiable query to add to the frames.
	 *
	 * @param predecessorTransition
	 * @param predecessorFrame
	 * @param prePred
	 * @return
	 * @throws AssertionError
	 */
	private IPredicate getInterpolant(final IcfgEdge predecessorTransition, final IPredicate predecessorFrame,
			final IPredicate prePred) throws AssertionError {

		final Term second = andPredTf(mScript.getScript(), predecessorFrame, predecessorTransition.getTransformula(),
				mCsToolkit.getModifiableGlobalsTable()
						.getModifiedBoogieVars(predecessorTransition.getPrecedingProcedure()));

		if (mLogger.isDebugEnabled()) {
			mLogger.debug(String.format("Converted frame %s and transformula %s to %s", predecessorFrame,
					predecessorTransition.getTransformula(), second));
		}

		final IPredicate secondPred = mPredicateUnifier.getOrConstructPredicate(second);

		// rename variables to primed constants
		final Set<IProgramVar> ppVars = prePred.getVars();
		final Map<Term, Term> substitutionMapping = new HashMap<>();
		final Map<Term, Term> reverseMapping = new HashMap<>();
		for (final IProgramVar var : ppVars) {
			substitutionMapping.put(var.getDefaultConstant(), var.getPrimedConstant());
			reverseMapping.put(var.getPrimedConstant(), var.getTermVariable());
		}

		final Term transformedPrePred =
				new Substitution(mScript, substitutionMapping).transform(prePred.getClosedFormula());

		final Pair<LBool, Term> interpolPair =
				SmtUtils.interpolateBinary(mScript.getScript(), transformedPrePred, secondPred.getClosedFormula());

		if (interpolPair.getFirst() == LBool.UNKNOWN) {
			return null;
		}

		if (interpolPair.getFirst() == LBool.SAT) {
			throw new AssertionError(String.format("Wrong interpolation query (is sat): %s  and  %s ",
					transformedPrePred, secondPred.getClosedFormula()));
		}

		// TODO: The interpolant is now full of variables that are constants and primed constant_pv_prime; we have to go
		// back to unprimed and un-constants

		for (final IProgramVar var : secondPred.getVars()) {
			reverseMapping.put(var.getPrimedConstant(), var.getTermVariable());
		}

		// unprime
		final Term transformedInterpolant =
				new Substitution(mScript, reverseMapping).transform(interpolPair.getSecond());

		final IPredicate interpolatedPreCondition = mPredicateUnifier.getOrConstructPredicate(transformedInterpolant);
		if (mLogger.isDebugEnabled()) {
			mLogger.debug(String.format("Interpolant: %s (%s from binInt(%s  %s))", interpolatedPreCondition,
					interpolPair.getSecond(), transformedPrePred, secondPred.getClosedFormula()));
		}
		return interpolatedPreCondition;
	}

	/**
	 * Generate a new proofobligation
	 *
	 * @param proofObligations
	 * @param proofObligation
	 * @param level
	 * @param predecessor
	 * @param preCondition
	 */
	private void addProofObligation(final Deque<ProofObligation> proofObligations,
			final ProofObligation proofObligation, final int level, final IcfgLocation predecessor,
			final IPredicate preCondition) {
		// add proof obligation
		final ProofObligation newProofObligation = new ProofObligation(preCondition, predecessor, mLevel - level + 1);

		mProofObligations.addFirst(newProofObligation);
		proofObligations.addFirst(proofObligation);
		proofObligations.addFirst(newProofObligation);
		if (mLogger.isDebugEnabled()) {
			mLogger.debug("New PO: " + newProofObligation);
		}
	}

	/**
	 * Update location's frame at level by toBoBlocked
	 *
	 * @param toBeBlocked
	 * @param location
	 * @param level
	 */
	private void updateFrames(final IPredicate toBeBlocked, final IcfgLocation location, final int level) {
		for (int i = 0; i <= level; i++) {
			IPredicate fTerm = mFrames.get(location).get(i).getSecond();
			final IPredicate negToBeBlocked = mPredicateUnifier.getPredicateFactory().not(toBeBlocked);
			fTerm = mPredicateUnifier.getPredicateFactory().and(fTerm, negToBeBlocked);
			fTerm = mPredicateUnifier.getOrConstructPredicate(fTerm);
			mFrames.get(location).set(i, new Pair<>(ChangedFrame.CHANGED, fTerm));
		}
		if (mLogger.isDebugEnabled()) {
			mLogger.debug("Frames: Updated");
			for (final Entry<IcfgLocation, List<Pair<ChangedFrame, IPredicate>>> entry : mFrames.entrySet()) {
				mLogger.debug("  " + entry.getKey().getDebugIdentifier() + ": " + entry.getValue().stream()
						.map(Pair<ChangedFrame, IPredicate>::toString).collect(Collectors.joining(",")));
			}
		}
	}

	/**
	 * Get a summarized procedure call.
	 *
	 * @param callLoc
	 * @param returnTrans
	 * @param globalVarsAssignments
	 * @param oldVarAssignments
	 * @param modifiableGlobals
	 * @return The trace as a pair of List of edges and a summarizing {@link UnmodifiableTransFormula}
	 */
	private Pair<List<LETTER>, UnmodifiableTransFormula> getProcedureTrace(final IcfgLocation callLoc,
			final IIcfgReturnTransition<?, ?> returnTrans, final UnmodifiableTransFormula globalVarsAssignments,
			final UnmodifiableTransFormula oldVarAssignments, final Set<IProgramNonOldVar> modifiableGlobals) {
		final IcfgLocation returnLoc = returnTrans.getSource();
		final List<UnmodifiableTransFormula> tfs = new ArrayList<>();
		tfs.add(returnTrans.getTransformula());
		int i = 0;
		int start = -1;
		int end = -1;

		for (final LETTER l : mTrace) {
			if (l.getSource().equals(callLoc.getLabel())) {
				start = i;
			} else if (l.getSource().equals(returnLoc.getLabel())) {
				end = i;
			}
			i++;
		}

		assert start != -1;
		assert end != -1;
		final List<LETTER> procedureTrace = new ArrayList<>(mTrace.subList(start, end));

		final List<UnmodifiableTransFormula> procTfs = new ArrayList<>();
		for (final LETTER letter : procedureTrace) {
			procTfs.add(letter.getTransformula());
		}

		final UnmodifiableTransFormula procTf = TransFormulaUtils.sequentialComposition(mLogger, mServices, mScript,
				true, false, false, XnfConversionTechnique.BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION,
				SimplificationTechnique.SIMPLIFY_DDA, procTfs);

		final UnmodifiableTransFormula procTfCallReturn = TransFormulaUtils.sequentialCompositionWithCallAndReturn(
				mScript, true, false, false, returnTrans.getLocalVarsAssignmentOfCall(), oldVarAssignments,
				globalVarsAssignments, procTf, returnTrans.getTransformula(), mLogger, mServices,
				XnfConversionTechnique.BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION, SimplificationTechnique.SIMPLIFY_DDA,
				mSymbolTable, modifiableGlobals);

		return new Pair<>(procedureTrace, procTfCallReturn);

	}

	/**
	 * Propagation-Phase, for finding invariants
	 */
	private boolean propagationPhase() {
		mLogger.debug("Begin Propagation Phase: \n");
		for (final Entry<IcfgLocation, List<Pair<ChangedFrame, IPredicate>>> locationTrace : mFrames.entrySet()) {
			final List<Pair<ChangedFrame, IPredicate>> frames = locationTrace.getValue();

			for (int i = 0; i < frames.size() - 1; i++) {
				/*
				 * if (frames.get(i).getFirst() == ChangedFrame.UNCHANGED || frames.get(i + 1).getFirst() ==
				 * ChangedFrame.UNCHANGED) { continue; }
				 */
				final IPredicate p1 = frames.get(i).getSecond();
				final IPredicate p2 = frames.get(i + 1).getSecond();

				if (p1.getFormula().equals(p2.getFormula()) && checkFrames(i)) {
					mLogger.debug("Spot: " + i);
					mInvarSpot = i;
					return true;
				}
			}
		}
		return false;
	}

	/**
	 * Check invariant candidate location i
	 *
	 * @param i
	 * @return
	 */
	private boolean checkFrames(final int i) {
		for (final Entry<IcfgLocation, List<Pair<ChangedFrame, IPredicate>>> locationTrace : mFrames.entrySet()) {
			if (mPpIcfg.getInitialNodes().contains(locationTrace.getKey())) {
				continue;
			}
			final List<Pair<ChangedFrame, IPredicate>> frames = locationTrace.getValue();

			final IPredicate p1 = frames.get(i).getSecond();
			final IPredicate p2 = frames.get(i + 1).getSecond();
			if (p1.getFormula().equals(p2.getFormula())) {
				continue;
			}
			return false;
		}
		return true;
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
	private Validity checkSatInternal(final IPredicate pre, final IInternalAction trans, final IPredicate post) {
		final IPredicate notP = not(post);
		final Validity result = mHtc.checkInternal(pre, trans, notP);

		if (mLogger.isDebugEnabled()) {
			mLogger.debug(String.format(" %s && %s && %s is %s", pre, trans, post,
					result == Validity.VALID ? "unsat" : result == Validity.INVALID ? "sat" : "unknown"));
		}
		assert result != Validity.NOT_CHECKED;
		return result;

	}

	private Validity checkSatCall(final IPredicate pre, final ICallAction trans, final IPredicate post) {
		final IPredicate notP = not(post);
		final Validity result = mHtc.checkCall(pre, trans, notP);

		if (mLogger.isDebugEnabled()) {
			mLogger.debug(String.format(" %s && %s && %s is %s", pre, trans, post,
					result == Validity.VALID ? "unsat" : result == Validity.INVALID ? "sat" : "unknown"));
		}
		assert result != Validity.NOT_CHECKED;
		return result;
	}

	private Validity checkSatReturn(final IPredicate pre, final IPredicate preHier, final IReturnAction trans,
			final IPredicate post) {
		final IPredicate notP = not(post);
		final Validity result = mHtc.checkReturn(pre, preHier, trans, notP);

		if (mLogger.isDebugEnabled()) {
			mLogger.debug(String.format(" %s && %s && %s && %s is %s", pre, preHier, trans, post,
					result == Validity.VALID ? "unsat" : result == Validity.INVALID ? "sat" : "unknown"));
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
	 * @return
	 */
	private IPredicate[] computeInterpolants() {
		mLogger.debug("Computing interpolants.");

		final Map<IcfgLocation, IPredicate> traceFrames = new HashMap<>();
		for (final Entry<IcfgLocation, List<Pair<ChangedFrame, IPredicate>>> entry : mFrames.entrySet()) {
			final IcfgLocation key = entry.getKey();
			final IcfgLocation actualLoc = key.getLabel();
			assert key != actualLoc : "Not a path program loc";
			assert mInvarSpot != -1 : "Invariants";

			final IPredicate pred = entry.getValue().get(mInvarSpot).getSecond();

			final IPredicate old = traceFrames.put(actualLoc, pred);
			assert old == null || old.equals(pred);

		}

		final Iterator<LETTER> traceIt = mTrace.iterator();
		final IPredicate[] interpolants = new IPredicate[mTrace.size() - 1];
		int i = 0;
		while (traceIt.hasNext()) {
			final LETTER l = traceIt.next();
			if (!traceIt.hasNext()) {
				// the last target is always false
				break;
			}

			final IPredicate lPreds = traceFrames.get(l.getTarget());
			assert lPreds != null;
			// final IPredicate lInterpolant =
			// mPredicateUnifier.getOrConstructPredicateForDisjunction(lPreds);
			interpolants[i] = lPreds;
			++i;
		}
		return interpolants;
	}

	/**
	 * Conjunct a {@link IPredicate} and a {@link TransFormula}
	 *
	 * @param script
	 * @param precond
	 * @param tf
	 * @param modifiableGlobalsPred
	 * @return
	 */
	private static Term andPredTf(final Script script, final IPredicate precond, final UnmodifiableTransFormula tf,
			final Set<IProgramNonOldVar> modifiableGlobalsPred) {

		final List<Term> conjuncts = new ArrayList<>();
		// add oldvar equalities for precond and tf
		final Set<IProgramNonOldVar> unprimedOldVarEqualities = new HashSet<>();
		final Set<IProgramNonOldVar> primedOldVarEqualities = new HashSet<>();

		findNonModifiablesGlobals(precond.getVars(), modifiableGlobalsPred, Collections.emptySet(),
				unprimedOldVarEqualities, primedOldVarEqualities);
		findNonModifiablesGlobals(tf.getInVars().keySet(), modifiableGlobalsPred, Collections.emptySet(),
				unprimedOldVarEqualities, primedOldVarEqualities);
		for (final IProgramNonOldVar bv : unprimedOldVarEqualities) {
			conjuncts.add(ModifiableGlobalsTable.constructConstantOldVarEquality(bv, false, script));
		}
		for (final IProgramNonOldVar bv : primedOldVarEqualities) {
			conjuncts.add(ModifiableGlobalsTable.constructConstantOldVarEquality(bv, true, script));
		}

		// add precond
		final Term precondRenamed = precond.getClosedFormula();
		assert precondRenamed != null;
		conjuncts.add(precondRenamed);

		// add tf
		final Term tfRenamed = tf.getClosedFormula();
		assert tfRenamed != null;
		conjuncts.add(tfRenamed);
		return SmtUtils.and(script, conjuncts);
	}

	/**
	 * Find all nonOldVars such that they are modifiable, their oldVar is in vars. Put the nonOldVar in
	 * nonModifiableGlobalsPrimed if the corresponding oldVar is in primedRequired.
	 *
	 * @param vars
	 * @param modifiableGlobalsPred
	 * @param primedRequired
	 * @param nonModifiableGlobalsUnprimed
	 * @param nonModifiableGlobalsPrimed
	 */
	private static void findNonModifiablesGlobals(final Set<IProgramVar> vars,
			final Set<IProgramNonOldVar> modifiableGlobalsPred, final Set<IProgramVar> primedRequired,
			final Set<IProgramNonOldVar> nonModifiableGlobalsUnprimed,
			final Set<IProgramNonOldVar> nonModifiableGlobalsPrimed) {
		for (final IProgramVar bv : vars) {
			if (bv instanceof IProgramOldVar) {
				final IProgramNonOldVar nonOldVar = ((IProgramOldVar) bv).getNonOldVar();
				if (modifiableGlobalsPred.contains(nonOldVar)) {
					// var modifiable, do nothing
				} else {
					if (primedRequired.contains(bv)) {
						nonModifiableGlobalsPrimed.add(nonOldVar);
					} else {
						nonModifiableGlobalsUnprimed.add(nonOldVar);
					}
				}
			}
		}
	}

	private IProgramExecution<IIcfgTransition<IcfgLocation>, Term> computeProgramExecution() {
		// TODO: construct a real IProgramExecution using
		// IcfgProgramExecutionBuilder (DD needs to refactor s.t. the
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
	public IProgramExecution<IIcfgTransition<IcfgLocation>, Term> getRcfgProgramExecution() {
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
