/*
 * Copyright (C) 2020 Jonas Werner (wernerj@informatik.uni-freiburg.de)
 * Copyright (C) 2020 University of Freiburg
 *
 * This file is part of the ULTIMATE accelerated interpolation library .
 *
 * The ULTIMATE framework is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE framework is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE accelerated interpolation library . If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE PDR library , or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE accelerated interpolation library grant you additional permission
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.lib.acceleratedinterpolation;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.IRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.ToolchainCanceledException;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.translation.IProgramExecution;
import de.uni_freiburg.informatik.ultimate.lib.acceleratedinterpolation.Interpolator.InterpolationMethod;
import de.uni_freiburg.informatik.ultimate.lib.acceleratedinterpolation.benchmark.AcceleratedInterpolationBenchmark;
import de.uni_freiburg.informatik.ultimate.lib.acceleratedinterpolation.benchmark.AcceleratedInterpolationBenchmark.AcceleratedInterpolationStatisticsDefinitions;
import de.uni_freiburg.informatik.ultimate.lib.acceleratedinterpolation.loopaccelerator.Accelerator;
import de.uni_freiburg.informatik.ultimate.lib.acceleratedinterpolation.loopaccelerator.Accelerator.AccelerationMethod;
import de.uni_freiburg.informatik.ultimate.lib.acceleratedinterpolation.loopdetector.Loopdetector;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdgeFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.debugidentifiers.StringDebugIdentifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaBuilder;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula.Infeasibility;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.PartialQuantifierElimination;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SolverBuilder;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SolverBuilder.SolverMode;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SolverBuilder.SolverSettings;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.interpolant.IInterpolatingTraceCheck;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.interpolant.InterpolantComputationStatus;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.interpolant.InterpolantComputationStatus.ItpErrorStatus;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateTransformer;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.SPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.TermDomainOperationProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.tracecheck.ITraceCheckPreferences;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.tracecheck.TraceCheckReasonUnknown;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.tracecheck.TraceCheckReasonUnknown.ExceptionHandlingCategory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.tracecheck.TraceCheckReasonUnknown.Reason;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.singletracecheck.TraceCheckUtils;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;
import de.uni_freiburg.informatik.ultimate.util.statistics.IStatisticsDataProvider;

/**
 *
 * @author Jonas Werner (wernerj@informatik.uni-freiburg.de)
 *
 * @param <LETTER>
 */
public class AcceleratedInterpolation<LETTER extends IIcfgTransition<?>> implements IInterpolatingTraceCheck<LETTER> {

	/**
	 * Indicate if the loop acceleration is bounded (-> precise: only one acceleration per loop), or unbounded (->
	 * underapproximation: multiple accelerations per loop)
	 */
	public enum AccelerationApproximationType {
		PRECISE, UNDERAPPROXIMATION
	}

	private final ILogger mLogger;
	private final ManagedScript mScript;
	private final IUltimateServiceProvider mServices;
	private final IRun<LETTER, IPredicate> mCounterexampleTrace;
	private final List<LETTER> mCounterexample;
	private final List<UnmodifiableTransFormula> mCounterexampleTf;
	private final IPredicateUnifier mPredUnifier;
	private final PredicateTransformer<Term, IPredicate, TransFormula> mPredTransformer;
	private final PredicateHelper<LETTER> mPredHelper;
	private final ITraceCheckPreferences mPrefs;
	private final IIcfg<? extends IcfgLocation> mIcfg;
	private final IcfgEdgeFactory mIcfgEdgeFactory;
	private LBool mIsTraceCorrect;
	private IPredicate[] mInterpolants;
	private IProgramExecution<IIcfgTransition<IcfgLocation>, Term> mFeasibleProgramExecution;
	private TraceCheckReasonUnknown mReasonUnknown;
	private boolean mTraceCheckFinishedNormally;
	private final IIcfgSymbolTable mSymbolTable;

	private final Map<IcfgLocation, Set<List<LETTER>>> mLoops;
	private final Map<IcfgLocation, LETTER> mLoopExitTransitions;
	private final Map<IcfgLocation, Pair<Integer, Integer>> mLoopSize;
	private final Map<IcfgLocation, List<UnmodifiableTransFormula>> mAccelerations;
	private final Accelerator<LETTER> mAccelerator;
	private final Loopdetector<LETTER> mLoopdetector;
	private AccelerationApproximationType mApproximationType;

	private final AcceleratedInterpolationBenchmark mAccelInterpolBench;

	public AcceleratedInterpolation(final ILogger logger, final ITraceCheckPreferences prefs,
			final ManagedScript script, final IPredicateUnifier predicateUnifier,
			final IRun<LETTER, IPredicate> counterexample) {
		mLogger = logger;
		mScript = script;
		mServices = prefs.getUltimateServices();
		mCounterexampleTrace = counterexample;
		mCounterexample = mCounterexampleTrace.getWord().asList();
		mPrefs = prefs;
		mAccelInterpolBench = new AcceleratedInterpolationBenchmark();
		mAccelInterpolBench.start(AcceleratedInterpolationStatisticsDefinitions.ACCELINTERPOL_OVERALL);

		mIcfg = mPrefs.getIcfgContainer();
		mIcfgEdgeFactory = mIcfg.getCfgSmtToolkit().getIcfgEdgeFactory();
		mPredUnifier = predicateUnifier;
		mAccelerations = new HashMap<>();
		mLogger.debug("Accelerated Interpolation engaged!");
		mInterpolants = new IPredicate[mCounterexample.size()];
		mInterpolants[0] = mPredUnifier.getTruePredicate();
		mInterpolants[mCounterexample.size() - 1] = mPredUnifier.getFalsePredicate();
		mSymbolTable = mIcfg.getCfgSmtToolkit().getSymbolTable();

		mAccelerator = new Accelerator<>(mLogger, mScript, mServices);

		mAccelInterpolBench.start(AcceleratedInterpolationStatisticsDefinitions.ACCELINTERPOL_LOOPDETECTOR);
		mLoopdetector = new Loopdetector<>(mCounterexample, mLogger, 1);
		mAccelInterpolBench.stop(AcceleratedInterpolationStatisticsDefinitions.ACCELINTERPOL_LOOPDETECTOR);

		mPredTransformer = new PredicateTransformer<>(mScript, new TermDomainOperationProvider(mServices, mScript));

		mPredHelper = new PredicateHelper<>(mPredUnifier, mPredTransformer, mLogger, mScript, mServices);
		mCounterexampleTf = mPredHelper.traceToListOfTfs(mCounterexample);

		mApproximationType = AccelerationApproximationType.PRECISE;
		mReasonUnknown = null;
		mTraceCheckFinishedNormally = true;
		/*
		 * Find loops in the trace.
		 */
		mLoops = mLoopdetector.getLoops();
		mLoopExitTransitions = mLoopdetector.getLoopExitTransitions();
		mLoopSize = mLoopdetector.getLoopSize();

		try {
			mAccelInterpolBench.start(AcceleratedInterpolationStatisticsDefinitions.ACCELINTERPOL_CORE);
			mIsTraceCorrect = acceleratedInterpolationCore();
			mLogger.info("Finished Analysing Program using " + mApproximationType.toString() + " loop Acceleration");
			mReasonUnknown = null;
			mTraceCheckFinishedNormally = true;
		} catch (final ToolchainCanceledException tce) {
			mTraceCheckFinishedNormally = false;
			mIsTraceCorrect = LBool.UNKNOWN;
			mReasonUnknown = new TraceCheckReasonUnknown(Reason.ULTIMATE_TIMEOUT, tce,
					ExceptionHandlingCategory.KNOWN_DEPENDING);
		} catch (final SMTLIBException e) {
			mTraceCheckFinishedNormally = false;
			mIsTraceCorrect = LBool.UNKNOWN;
			mReasonUnknown = TraceCheckReasonUnknown.constructReasonUnknown(e);
		} finally {
			mAccelInterpolBench.stopAllStopwatches();
			mLogger.debug("Finished");
		}
	}

	/**
	 * Main function of accelInteprol
	 */
	private LBool acceleratedInterpolationCore() {
		/*
		 * After finding loops in the trace, start calculating loop accelerations.
		 */
		final Iterator<Entry<IcfgLocation, Set<List<LETTER>>>> loopheadIterator = mLoops.entrySet().iterator();
		while (loopheadIterator.hasNext()) {
			final Entry<IcfgLocation, Set<List<LETTER>>> loophead = loopheadIterator.next();
			boolean accelerationFinishedCorrectly = false;
			final List<UnmodifiableTransFormula> accelerations = new ArrayList<>();
			mAccelInterpolBench.start(AcceleratedInterpolationStatisticsDefinitions.ACCELINTERPOL_LOOPACCELERATOR);
			for (final List<LETTER> loop : loophead.getValue()) {
				final UnmodifiableTransFormula loopRelation = mPredHelper.traceToTf(loop);
				final UnmodifiableTransFormula acceleratedLoopRelation =
						mAccelerator.accelerateLoop(loopRelation, AccelerationMethod.FAST_UPR);
				if (!mAccelerator.accelerationFinishedCorrectly()) {
					accelerationFinishedCorrectly = false;
					break;
				}
				accelerationFinishedCorrectly = true;
				final Term t = PartialQuantifierElimination.tryToEliminate(mServices, mLogger, mScript,
						acceleratedLoopRelation.getFormula(), SimplificationTechnique.SIMPLIFY_BDD_FIRST_ORDER,
						XnfConversionTechnique.BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION);
				final TransFormulaBuilder tfb = new TransFormulaBuilder(acceleratedLoopRelation.getInVars(),
						acceleratedLoopRelation.getOutVars(), true, Collections.emptySet(), true,
						Collections.emptySet(), false);
				for (final TermVariable auxVar : acceleratedLoopRelation.getAuxVars()) {
					tfb.addAuxVar(auxVar);
				}
				tfb.setFormula(t);
				tfb.setInfeasibility(Infeasibility.NOT_DETERMINED);
				final UnmodifiableTransFormula accelerationNoQuantifiersTf = tfb.finishConstruction(mScript);
				accelerations.add(accelerationNoQuantifiersTf);
			}
			if (!accelerationFinishedCorrectly) {
				loopheadIterator.remove();
				break;
			}
			mAccelInterpolBench.stop(AcceleratedInterpolationStatisticsDefinitions.ACCELINTERPOL_LOOPACCELERATOR);
			if (accelerations.size() > 1) {
				mApproximationType = AccelerationApproximationType.UNDERAPPROXIMATION;
			}
			mAccelerations.put(loophead.getKey(), accelerations);
		}

		/*
		 * Use new Script for interpolation:
		 */
		final ManagedScript ipScript = constructManagedScriptForInterpolation();
		/*
		 * Or use CFG's script for interpolation:
		 */
		// final ManagedScript ipScript = mScript;
		final Interpolator<LETTER> interpolator =
				new Interpolator<>(mPredUnifier, mPredTransformer, mLogger, ipScript, mServices, mPredHelper, mPrefs);

		/*
		 * No loops -> no acceleration
		 */
		if (mLoops.isEmpty()) {
			mLogger.debug("No loops found in this trace.");
			interpolator.generateInterpolants(InterpolationMethod.CRAIG_NESTED, mCounterexampleTrace);
			if (interpolator.isTraceCorrect() == LBool.UNSAT) {
				mInterpolants = interpolator.getInterpolants();
				return LBool.UNSAT;
			}
			return LBool.SAT;
		}

		/*
		 * translate the given trace into a meta trace which makes use of the loop acceleration.
		 */
		final NestedRun<LETTER, IPredicate> traceScheme = generateMetaTrace();

		interpolator.generateInterpolants(InterpolationMethod.CRAIG_NESTED, traceScheme);
		if (interpolator.isTraceCorrect() == LBool.UNSAT) {
			final IPredicate[] tempInterpolants = interpolator.getInterpolants();
			final IPredicate[] inductiveInterpolants = constructInductive(tempInterpolants);

			// mInterpolants = interpolator.getInterpolants();
			mInterpolants = inductiveInterpolants;
			return LBool.UNSAT;
		}
		return LBool.SAT;
	}

	/**
	 * Transforms the tracescheme interpolants to inductive interpolants Problem
	 */
	private IPredicate[] constructInductive(final IPredicate[] preds) {
		final IPredicate[] actualInterpolants = new IPredicate[mCounterexample.size() - 1];
		int cnt = 0;
		for (int i = 0; i < actualInterpolants.length; i++) {
			final IcfgLocation target = mCounterexample.get(i).getTarget();
			/*
			 * When the next location is a loophead, use loopaccelerations
			 */
			if (mAccelerations.containsKey(target)) {
				final Pair<Integer, Integer> loopSize = mLoopSize.get(target);
				final List<UnmodifiableTransFormula> loopAccelerations = new ArrayList<>(mAccelerations.get(target));

				final List<Term> loopAccelerationsForEntryLocation = new ArrayList<>();
				loopAccelerationsForEntryLocation.add(preds[cnt].getFormula());
				int currentPredCounter = cnt;
				int currentIterationCounter = 0;
				final int maxLoopPredicates = 2 * loopAccelerations.size();
				/*
				 * In case there are multiple loop accelerations, construct post of meta trace's interpolant and
				 * corresponding loop acceleration
				 */
				while (currentPredCounter < maxLoopPredicates) {
					final IPredicate loopEntryInterpolantMetaTrace = preds[currentPredCounter];
					final UnmodifiableTransFormula loopAccelerationForCorrespondingLoop =
							loopAccelerations.get(currentIterationCounter);
					final Term postInterpolantLoopacceleration = mPredTransformer.strongestPostcondition(
							loopEntryInterpolantMetaTrace, loopAccelerationForCorrespondingLoop);
					loopAccelerationsForEntryLocation.add(postInterpolantLoopacceleration);
					currentIterationCounter++;
					currentPredCounter = currentPredCounter + 2;
				}
				cnt = cnt + maxLoopPredicates - 1;
				/*
				 * Then construct a disjunction of all possible loop accelerations posts at the loop head
				 */
				final Term loopAccelerationsForEntryLocationDisjunction =
						SmtUtils.or(mScript.getScript(), loopAccelerationsForEntryLocation);

				final IPredicate interpolantPred =
						mPredUnifier.getOrConstructPredicate(loopAccelerationsForEntryLocationDisjunction);

				actualInterpolants[i] = interpolantPred;
				int j = i + 1;
				/*
				 * Because the meta trace interpolants are too few, we need to post through the whole loop to get an
				 * inductive interpolant sequence
				 */
				while (j < loopSize.getSecond() + 1) {
					final UnmodifiableTransFormula transRel = mCounterexample.get(j).getTransformula();
					final Term loopPostTerm =
							mPredTransformer.strongestPostcondition(actualInterpolants[j - 1], transRel);
					actualInterpolants[j] = mPredUnifier.getOrConstructPredicate(loopPostTerm);
					j++;
				}
				i = loopSize.getSecond() - 1;
			} else {
				IPredicate prevInterpol;
				/*
				 * post does not work well with false
				 */
				if (SmtUtils.isFalseLiteral(preds[cnt].getFormula()) && i != 0) {
					prevInterpol = actualInterpolants[i - 1];
					final Term post = mPredTransformer.strongestPostcondition(prevInterpol,
							mCounterexample.get(i).getTransformula());
					prevInterpol = mPredUnifier.getOrConstructPredicate(post);
				} else {
					prevInterpol = preds[cnt];
				}

				actualInterpolants[i] = prevInterpol;
			}
			cnt++;
		}
		return actualInterpolants;
	}

	/**
	 * It might be necessary to create a fresh mScript instance for the interpolation, in particular if you want to
	 * interpolate multiple times.
	 *
	 * @return
	 * @throws AssertionError
	 */
	private ManagedScript constructManagedScriptForInterpolation() throws AssertionError {
		final SolverSettings solverSettings = SolverBuilder.constructSolverSettings().setUseFakeIncrementalScript(false)
				.setSolverMode(SolverMode.Internal_SMTInterpol);
		final String solverId = solverSettings.getBaseNameOfDumpedScript();
		final Script tcSolver = SolverBuilder.buildAndInitializeSolver(mServices, solverSettings, solverId);
		final ManagedScript mgdScriptTc = new ManagedScript(mServices, tcSolver);
		mPrefs.getIcfgContainer().getCfgSmtToolkit().getSmtFunctionsAndAxioms().transferAllSymbols(tcSolver);
		return mgdScriptTc;
	}

	/**
	 * Transform the counterexample to a meta trace by "pulling" loopheads into two locations. A meta trace is a given
	 * error trace where the loops have been replaced by their accelerations as one transition.
	 *
	 * @return
	 */
	private NestedRun<LETTER, IPredicate> generateMetaTrace() {
		final List<LETTER> counterExampleNonAccelerated = new ArrayList<>(mCounterexample);
		final List<UnmodifiableTransFormula> counterExampleAccelerated = new ArrayList<>();
		final List<LETTER> counterExampleAcceleratedLetter = new ArrayList<>();
		final ArrayList<IPredicate> traceStates = new ArrayList<>();
		final ArrayList<IPredicate> acceleratedTraceSchemeStates = new ArrayList<>();
		traceStates.addAll(mCounterexampleTrace.getStateSequence());
		for (int i = 0; i < counterExampleNonAccelerated.size(); i++) {
			final LETTER l = counterExampleNonAccelerated.get(i);
			counterExampleAccelerated.add(l.getTransformula());
			counterExampleAcceleratedLetter.add(l);
			acceleratedTraceSchemeStates.add(traceStates.get(i));
			/*
			 * Search for loops.
			 */
			if (!mLoops.containsKey(l.getTarget())) {
				continue;
			}
			final IcfgLocation target = l.getTarget();
			final PredicateFactory predFactory = new PredicateFactory(mServices, mScript, mSymbolTable);
			/*
			 * Construct new exit locations, which is the loophead just primed And a new transition whose transformula
			 * is the loop acceleration.
			 */
			final LETTER loopExitTransition = mLoopExitTransitions.get(target);
			final IcfgLocation loopExitLocation = loopExitTransition.getTarget();
			final StringDebugIdentifier newExitId =
					new StringDebugIdentifier(loopExitLocation.getDebugIdentifier().toString() + "_primed");

			/*
			 * Construct new SPredicates as needed for nested word generation.
			 */
			final Term newExitTransitionDefaultVars = mPredHelper.normalizeTerm(loopExitTransition.getTransformula());
			final SPredicate newExitSPred = predFactory.newSPredicate(loopExitLocation, newExitTransitionDefaultVars);
			final IcfgLocation newExitLocation = new IcfgLocation(newExitId, loopExitLocation.getProcedure());

			/**
			 * TODO: Deal with unsafe cast!
			 */
			final LETTER newLoopExitTransition = (LETTER) mIcfgEdgeFactory.createInternalTransition(newExitLocation,
					loopExitLocation, loopExitLocation.getPayload(), loopExitTransition.getTransformula());

			final List<UnmodifiableTransFormula> accelerations = mAccelerations.get(target);

			/*
			 * In case we have multiple loop accelerations for one loop, like when there are more than one path through
			 * it, construct a meta trace where each loop acceleration is disjunct but connected with an epsilon
			 * transition.
			 */
			if (accelerations.size() > 1) {
				for (int j = 0; j < accelerations.size() - 1; j++) {
					final UnmodifiableTransFormula loopAcceleration = accelerations.get(j);

					final LETTER acceleratedTransition = (LETTER) mIcfgEdgeFactory.createInternalTransition(target,
							newExitLocation, target.getPayload(), loopAcceleration);

					final UnmodifiableTransFormula epsilon = constructEpsilon(loopAcceleration);
					final LETTER epsilonTransition = (LETTER) mIcfgEdgeFactory.createInternalTransition(newExitLocation,
							target, target.getPayload(), epsilon);

					final Term acceleratedTransitionDefaultVars = mPredHelper.normalizeTerm(loopAcceleration);
					final Term epsilonDefaultVars = mPredHelper.normalizeTerm(epsilon);
					final SPredicate acceleratedSPred =
							predFactory.newSPredicate(newExitLocation, acceleratedTransitionDefaultVars);
					final SPredicate epsilonSPred = predFactory.newSPredicate(target, epsilonDefaultVars);

					counterExampleAcceleratedLetter.add(acceleratedTransition);
					counterExampleAcceleratedLetter.add(epsilonTransition);

					acceleratedTraceSchemeStates.add(acceleratedSPred);
					acceleratedTraceSchemeStates.add(epsilonSPred);
				}
			}

			final UnmodifiableTransFormula lastLoopAcceleration = accelerations.get(accelerations.size() - 1);
			/**
			 * TODO: Deal with unsafe cast!
			 */
			final LETTER lastAcceleratedTransition = (LETTER) mIcfgEdgeFactory.createInternalTransition(target,
					newExitLocation, l.getTarget().getPayload(), lastLoopAcceleration);
			final Term lastAcceleratedTransitionDefaultVars = mPredHelper.normalizeTerm(lastLoopAcceleration);

			counterExampleAcceleratedLetter.add(lastAcceleratedTransition);
			counterExampleAcceleratedLetter.add(newLoopExitTransition);

			final SPredicate lastAcceleratedSPred =
					predFactory.newSPredicate(newExitLocation, lastAcceleratedTransitionDefaultVars);

			acceleratedTraceSchemeStates.add(lastAcceleratedSPred);
			acceleratedTraceSchemeStates.add(newExitSPred);
			final Pair<Integer, Integer> loopSize = mLoopSize.get(l.getTarget());
			i = loopSize.getSecond();
		}

		acceleratedTraceSchemeStates.add(traceStates.get(counterExampleNonAccelerated.size()));

		/*
		 * Turn the new trace into a nested word for easier interpolation
		 */
		final NestedWord<LETTER> traceSchemeNestedWord = TraceCheckUtils.toNestedWord(counterExampleAcceleratedLetter);
		final NestedRun<LETTER, IPredicate> traceSchemeRun =
				new NestedRun<>(traceSchemeNestedWord, acceleratedTraceSchemeStates);
		return traceSchemeRun;
	}

	/**
	 * Constructs a Transformula where every variable is unchanged.
	 * 
	 * @param tf
	 * @return
	 */
	private UnmodifiableTransFormula constructEpsilon(final UnmodifiableTransFormula tf) {
		final Map<IProgramVar, TermVariable> inVars = tf.getInVars();
		final Map<IProgramVar, TermVariable> outVars = tf.getOutVars();
		final ArrayList<Term> lhs = new ArrayList<>(inVars.values());
		final ArrayList<Term> rhs = new ArrayList<>(outVars.values());

		final Term equality = SmtUtils.pairwiseEquality(mScript.getScript(), lhs, rhs);
		final TransFormulaBuilder tfb = new TransFormulaBuilder(inVars, outVars, true, null, false, null, true);
		tfb.setFormula(equality);
		tfb.setInfeasibility(Infeasibility.NOT_DETERMINED);
		return tfb.finishConstruction(mScript);
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

	@Override
	public LBool isCorrect() {
		return mIsTraceCorrect;
	}

	@Override
	public IPredicate getPrecondition() {
		return mPredUnifier.getTruePredicate();
	}

	@Override
	public IPredicate getPostcondition() {
		return mPredUnifier.getFalsePredicate();
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
	public TraceCheckReasonUnknown getTraceCheckReasonUnknown() {
		return mReasonUnknown;
	}

	@Override
	public boolean wasTracecheckFinishedNormally() {
		return mTraceCheckFinishedNormally;
	}

	@Override
	public List<LETTER> getTrace() {
		return mCounterexample;
	}

	@Override
	public IPredicate[] getInterpolants() {
		return mInterpolants;
	}

	@Override
	public IPredicateUnifier getPredicateUnifier() {
		return mPredUnifier;
	}

	@Override
	public boolean isPerfectSequence() {
		return isCorrect() == LBool.UNSAT;
	}

	@Override
	public InterpolantComputationStatus getInterpolantComputationStatus() {
		if (isCorrect() == LBool.UNSAT) {
			return new InterpolantComputationStatus();
		} else if (isCorrect() == LBool.SAT) {
			return new InterpolantComputationStatus(ItpErrorStatus.TRACE_FEASIBLE, null);
		} else {
			throw new UnsupportedOperationException();
		}
	}

	@Override
	public IStatisticsDataProvider getStatistics() {
		// TODO Auto-generated method stub
		return null;
	}

}
