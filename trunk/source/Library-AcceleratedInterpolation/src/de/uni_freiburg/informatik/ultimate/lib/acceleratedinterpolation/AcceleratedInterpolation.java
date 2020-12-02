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
import java.util.HashSet;
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
import de.uni_freiburg.informatik.ultimate.lib.acceleratedinterpolation.MetaTraceTransformer.MetaTraceApplicationMethod;
import de.uni_freiburg.informatik.ultimate.lib.acceleratedinterpolation.benchmark.AcceleratedInterpolationBenchmark;
import de.uni_freiburg.informatik.ultimate.lib.acceleratedinterpolation.benchmark.AcceleratedInterpolationBenchmark.AcceleratedInterpolationStatisticsDefinitions;
import de.uni_freiburg.informatik.ultimate.lib.acceleratedinterpolation.loopaccelerator.Accelerator;
import de.uni_freiburg.informatik.ultimate.lib.acceleratedinterpolation.loopdetector.ILoopdetector;
import de.uni_freiburg.informatik.ultimate.lib.acceleratedinterpolation.loopdetector.Loopdetector;
import de.uni_freiburg.informatik.ultimate.lib.acceleratedinterpolation.looppreprocessor.ILoopPreprocessor;
import de.uni_freiburg.informatik.ultimate.lib.acceleratedinterpolation.looppreprocessor.LoopPreprocessorFastUPR;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdgeFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.debugidentifiers.StringDebugIdentifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaBuilder;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.PartialQuantifierElimination;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.interpolant.IInterpolatingTraceCheck;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.interpolant.InterpolantComputationStatus;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.interpolant.InterpolantComputationStatus.ItpErrorStatus;
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
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.solverbuilder.SolverBuilder;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.solverbuilder.SolverBuilder.SolverMode;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.solverbuilder.SolverBuilder.SolverSettings;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.singletracecheck.TraceCheckUtils;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;
import de.uni_freiburg.informatik.ultimate.util.statistics.IStatisticsDataProvider;

/**
 *
 * @author Jonas Werner (wernerj@informatik.uni-freiburg.de)
 *
 * @param <L>
 */
public class AcceleratedInterpolation<L extends IIcfgTransition<?>> implements IInterpolatingTraceCheck<L> {

	/**
	 * Indicate if the loop acceleration is bounded (-> precise: only one acceleration per loop), or unbounded (->
	 * underapproximation: multiple accelerations per loop)
	 */
	public enum AccelerationApproximationType {
		PRECISE, UNDERAPPROXIMATION
	}

	/**
	 * How to deal with loops.
	 */
	public enum AccelerationMethod {
		NONE, FAST_UPR, UNDERAPPROXIMATION, OVERAPPROXIMATION_WERNER
	}

	private final ILogger mLogger;
	private final ManagedScript mScript;
	private final IUltimateServiceProvider mServices;
	private final IRun<L, IPredicate> mCounterexampleTrace;
	private final List<L> mCounterexample;
	private final List<UnmodifiableTransFormula> mCounterexampleTf;
	private final IPredicateUnifier mPredUnifier;
	private final PredicateTransformer<Term, IPredicate, TransFormula> mPredTransformer;
	private final PredicateHelper<L> mPredHelper;
	private final ITraceCheckPreferences mPrefs;
	private final IIcfg<? extends IcfgLocation> mIcfg;
	private final IcfgEdgeFactory mIcfgEdgeFactory;
	private LBool mIsTraceCorrect;
	private IPredicate[] mInterpolants;
	private IProgramExecution<L, Term> mFeasibleProgramExecution;
	private TraceCheckReasonUnknown mReasonUnknown;
	private boolean mTraceCheckFinishedNormally;
	private final IIcfgSymbolTable mSymbolTable;
	private final SimplificationTechnique mSimplificationTechnique;

	private final Map<IcfgLocation, Set<List<L>>> mLoops;
	private final Map<IcfgLocation, Set<List<UnmodifiableTransFormula>>> mLoopsAsTf;
	private final Map<IcfgLocation, Set<List<UnmodifiableTransFormula>>> mNestedLoopsAsTf;
	private final Map<IcfgLocation, IcfgLocation> mNestingRelation;
	private final Map<IcfgLocation, Set<List<L>>> mNestedLoops;
	private Map<IcfgLocation, List<UnmodifiableTransFormula>> mNestedLoopsTf;
	private Map<IcfgLocation, List<UnmodifiableTransFormula>> mLoopsTf;
	private final Map<IcfgLocation, L> mLoopExitTransitions;
	private final Map<IcfgLocation, Pair<Integer, Integer>> mLoopSize;
	private final Map<IcfgLocation, List<UnmodifiableTransFormula>> mAccelerations;
	private final Accelerator<L> mAccelerator;
	private final ILoopdetector<IcfgLocation, L> mLoopdetector;
	private AccelerationApproximationType mApproximationType;
	private final MetaTraceApplicationMethod mMetaTraceApplicationMethod;
	private final MetaTraceTransformer<L> mMetaTraceTransformer;

	private final AccelerationMethod mAccelerationMethod;

	private final AcceleratedInterpolationBenchmark mAccelInterpolBench;
	private final Class<L> mTransitionClazz;

	/**
	 * Interpolation using loopacceleration
	 *
	 * @param logger
	 * @param prefs
	 * @param script
	 * @param predicateUnifier
	 * @param counterexample
	 * @param transitionClazz
	 */
	public AcceleratedInterpolation(final ILogger logger, final ITraceCheckPreferences prefs,
			final ManagedScript script, final IPredicateUnifier predicateUnifier,
			final IRun<L, IPredicate> counterexample, final Class<L> transitionClazz,
			final AccelerationMethod accelerationMethod) {
		mLogger = logger;
		mScript = script;
		mTransitionClazz = transitionClazz;
		mServices = prefs.getUltimateServices();
		mCounterexampleTrace = counterexample;
		mCounterexample = mCounterexampleTrace.getWord().asList();
		mPrefs = prefs;
		mSimplificationTechnique = mPrefs.getSimplificationTechnique();
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

		mAccelerationMethod = accelerationMethod;

		mAccelerator = new Accelerator<>(mLogger, mScript, mServices, mSymbolTable);
		mAccelInterpolBench.start(AcceleratedInterpolationStatisticsDefinitions.ACCELINTERPOL_LOOPDETECTOR);
		mLoopdetector = new Loopdetector<>(mCounterexample, mLogger, 1, mIcfg);
		mAccelInterpolBench.stop(AcceleratedInterpolationStatisticsDefinitions.ACCELINTERPOL_LOOPDETECTOR);

		mPredTransformer = new PredicateTransformer<>(mScript, new TermDomainOperationProvider(mServices, mScript));

		mPredHelper = new PredicateHelper<>(mPredUnifier, mPredTransformer, mLogger, mScript, mServices);
		mMetaTraceTransformer = new MetaTraceTransformer<>(mLogger, mScript, mCounterexample, mPredUnifier, mServices,
				mPredTransformer);
		mCounterexampleTf = mPredHelper.traceToListOfTfs(mCounterexample);

		mApproximationType = AccelerationApproximationType.PRECISE;
		mMetaTraceApplicationMethod = MetaTraceApplicationMethod.ONLY_AT_FIRST_LOOP_ENTRY;

		mReasonUnknown = null;
		mTraceCheckFinishedNormally = true;
		/*
		 * Find loops in the trace.
		 */
		mLoops = mLoopdetector.getLoops();
		mLoopsAsTf = mLoopdetector.getLoopsTf();
		mNestedLoopsAsTf = mLoopdetector.getNestedLoopsTf();
		mNestingRelation = mLoopdetector.getNestingRelation();
		mNestedLoops = mLoopdetector.getNestedLoops();
		mLoopSize = mLoopdetector.getLoopSize();
		mLoopExitTransitions = mLoopdetector.getLoopExitTransitions();
		mNestedLoopsTf = new HashMap<>();

		try {
			mAccelInterpolBench.start(AcceleratedInterpolationStatisticsDefinitions.ACCELINTERPOL_CORE);
			mIsTraceCorrect = acceleratedInterpolationCore();

			/*
			 * Quick fix for unsound false: Sometimes the interpolator returns unknown.
			 */
			if (mIsTraceCorrect == LBool.UNKNOWN) {
				mReasonUnknown = new TraceCheckReasonUnknown(Reason.SOLVER_RESPONSE_OTHER, null,
						ExceptionHandlingCategory.KNOWN_DEPENDING);
				mTraceCheckFinishedNormally = true;
			} else {
				mTraceCheckFinishedNormally = true;
				mReasonUnknown = null;
			}
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
	 * Main function of accelInterpol
	 */
	private LBool acceleratedInterpolationCore() {
		/*
		 * After finding loops in the trace, start calculating loop accelerations.
		 */
		final ILoopPreprocessor<IcfgLocation, UnmodifiableTransFormula> loopPreprocessor =
				new LoopPreprocessorFastUPR<>(mLogger, mScript, mServices, mPredUnifier, mPredHelper,
						mIcfg.getCfgSmtToolkit());
		if (!mNestedLoops.isEmpty()) {
			final Map<IcfgLocation, Set<List<L>>> nestedLoopFiltered =
					new HashMap<IcfgLocation, Set<List<L>>>(mNestedLoops);
			for (final Entry<IcfgLocation, Set<List<L>>> nestedLoop : nestedLoopFiltered.entrySet()) {
				if (nestedLoop.getValue() == null) {
					mNestedLoops.remove(nestedLoop.getKey());
					continue;
				}
			}
			mNestedLoopsTf = loopPreprocessor.preProcessLoop(mNestedLoopsAsTf);
			for (final Entry<IcfgLocation, IcfgLocation> nesting : mNestingRelation.entrySet()) {
				accelerateNestedLoops(nesting.getKey(), nesting.getValue());
			}
		}

		mLoopsTf = loopPreprocessor.preProcessLoop(mLoopsAsTf);
		mLogger.debug("Done Preprocessing");

		final Iterator<Entry<IcfgLocation, Set<List<L>>>> loopheadIterator = mLoops.entrySet().iterator();
		while (loopheadIterator.hasNext()) {
			final Entry<IcfgLocation, Set<List<L>>> loophead = loopheadIterator.next();
			final List<UnmodifiableTransFormula> loopTf = mLoopsTf.get(loophead.getKey());
			boolean accelerationFinishedCorrectly = false;
			final List<UnmodifiableTransFormula> accelerations = new ArrayList<>();
			mAccelInterpolBench.start(AcceleratedInterpolationStatisticsDefinitions.ACCELINTERPOL_LOOPACCELERATOR);
			for (final UnmodifiableTransFormula loop : loopTf) {
				mLogger.debug("Starting acceleration");
				final UnmodifiableTransFormula acceleratedLoopRelation =
						mAccelerator.accelerateLoop(loop, loophead.getKey(), mAccelerationMethod);
				if (!mAccelerator.accelerationFinishedCorrectly()) {
					mLogger.debug("No acceleration found");
					accelerationFinishedCorrectly = false;
					break;
				}
				accelerationFinishedCorrectly = true;
				Term t = mPredHelper.makeReflexive(acceleratedLoopRelation.getFormula(), acceleratedLoopRelation);
				t = PartialQuantifierElimination.tryToEliminate(mServices, mLogger, mScript, t,
						mSimplificationTechnique, XnfConversionTechnique.BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION);
				final UnmodifiableTransFormula tf = mPredHelper.normalizeTerm(t, acceleratedLoopRelation, true);

				mLogger.debug("Computed Acceleration: " + tf.getFormula().toStringDirect());
				accelerations.add(tf);
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
			mLogger.info("Starting analysis with loop acceleration approximation " + mApproximationType.toString());
		}

		// Use new Script for interpolation:
		final ManagedScript ipScript = constructManagedScriptForInterpolation();
		final Interpolator<L> interpolator =
				new Interpolator<>(mPredUnifier, mPredTransformer, mLogger, ipScript, mServices, mPrefs);

		if (mLoops.isEmpty() || mAccelerations.isEmpty()) {
			/*
			 * No loops or no acceleration
			 */
			mLogger.info("No loops in this trace, falling back to nested interpolation");
			interpolator.generateInterpolants(InterpolationMethod.CRAIG_NESTED, mCounterexampleTrace);
			mInterpolants = interpolator.getInterpolants();
		} else {
			/*
			 * translate the given trace into a meta trace which makes use of the loop acceleration.
			 */
			final NestedRun<L, IPredicate> metaTrace = generateMetaTrace();
			if (mLogger.isDebugEnabled()) {
				mLogger.debug("Meta-Trace: ");
				for (int i = 0; i < metaTrace.getLength() - 1; i++) {
					mLogger.debug(metaTrace.getSymbol(i).getTransformula().toStringDirect());
				}
			}
			interpolator.generateInterpolants(InterpolationMethod.CRAIG_NESTED, metaTrace);
			if (interpolator.getTraceCheckResult() == LBool.UNSAT) {
				final IPredicate[] tempInterpolants = interpolator.getInterpolants();
				if (mLogger.isDebugEnabled()) {
					mLogger.debug("Is " + interpolator.getTraceCheckResult().toString());
				}
				final IPredicate[] inductiveInterpolants = mMetaTraceTransformer.getInductiveLoopInterpolants(
						tempInterpolants, mAccelerations, mLoopSize, mMetaTraceApplicationMethod);
				mInterpolants = inductiveInterpolants;
			}
		}
		return interpolator.getTraceCheckResult();
	}

	private IProgramExecution<L, Term> computeProgramExecution() {
		// TODO: construct a real IProgramExecution using
		// IcfgProgramExecutionBuilder (DD needs to refactor s.t. the
		// class becomes available here).
		if (mIsTraceCorrect == LBool.SAT) {
			return IProgramExecution.emptyExecution(Term.class, mTransitionClazz);
		}
		return null;
	}

	/**
	 * Constructs a Transformula where every variable is unchanged.
	 *
	 * @param tf
	 * @return
	 */
	private UnmodifiableTransFormula constructEpsilon() {
		// final Map<IProgramVar, TermVariable> inVars = tf.getInVars();
		// final Map<IProgramVar, TermVariable> outVars = tf.getOutVars();
		// final ArrayList<Term> lhs = new ArrayList<>(inVars.values());
		// final ArrayList<Term> rhs = new ArrayList<>(outVars.values());
		//
		// final Term equality = SmtUtils.pairwiseEquality(mScript.getScript(), lhs, rhs);
		// final TransFormulaBuilder tfb = new TransFormulaBuilder(inVars, outVars, true, null, false, null, true);
		// tfb.setFormula(equality);
		// tfb.setInfeasibility(Infeasibility.NOT_DETERMINED);
		return TransFormulaBuilder.getTrivialTransFormula(mScript);
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
	private NestedRun<L, IPredicate> generateMetaTrace() {
		final List<L> counterExampleNonAccelerated = new ArrayList<>(mCounterexample);
		final List<UnmodifiableTransFormula> counterExampleAccelerated = new ArrayList<>();
		final List<L> counterExampleAcceleratedLetter = new ArrayList<>();
		final ArrayList<IPredicate> traceStates = new ArrayList<>();
		final ArrayList<IPredicate> acceleratedTraceSchemeStates = new ArrayList<>();
		traceStates.addAll(mCounterexampleTrace.getStateSequence());
		for (int i = 0; i < counterExampleNonAccelerated.size(); i++) {
			final L l = counterExampleNonAccelerated.get(i);
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
			final L loopExitTransition = mLoopExitTransitions.get(target);
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
			final L newLoopExitTransition = (L) mIcfgEdgeFactory.createInternalTransition(newExitLocation,
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

					final L acceleratedTransition = (L) mIcfgEdgeFactory.createInternalTransition(target,
							newExitLocation, target.getPayload(), loopAcceleration);

					final UnmodifiableTransFormula epsilon = constructEpsilon();
					final L epsilonTransition = (L) mIcfgEdgeFactory.createInternalTransition(newExitLocation, target,
							target.getPayload(), epsilon);

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
			final L lastAcceleratedTransition = (L) mIcfgEdgeFactory.createInternalTransition(target, newExitLocation,
					l.getTarget().getPayload(), lastLoopAcceleration);
			final Term lastAcceleratedTransitionDefaultVars = mPredHelper.normalizeTerm(lastLoopAcceleration);
			counterExampleAcceleratedLetter.add(lastAcceleratedTransition);
			counterExampleAcceleratedLetter.add(newLoopExitTransition);
			final SPredicate lastAcceleratedSPred =
					predFactory.newSPredicate(newExitLocation, lastAcceleratedTransitionDefaultVars);
			acceleratedTraceSchemeStates.add(lastAcceleratedSPred);
			acceleratedTraceSchemeStates.add(newExitSPred);
			final Pair<Integer, Integer> loopSize = mLoopSize.get(l.getTarget());
			i = i + loopSize.getSecond() - loopSize.getFirst() + 1;
		}

		acceleratedTraceSchemeStates.add(traceStates.get(counterExampleNonAccelerated.size()));

		/*
		 * Turn the new trace into a nested word for easier interpolation
		 */
		final NestedWord<L> traceSchemeNestedWord = TraceCheckUtils.toNestedWord(counterExampleAcceleratedLetter);

		if (mLogger.isDebugEnabled()) {
			mLogger.debug("Current trace");
			mCounterexample.forEach(a -> mLogger.debug(a.getTransformula()));

			mLogger.debug("Simpified acceleration");
			for (final L letter : traceSchemeNestedWord) {
				mLogger.debug(SmtUtils.simplify(mScript, letter.getTransformula().getFormula(), mServices,
						SimplificationTechnique.SIMPLIFY_DDA).toStringDirect());
				mLogger.debug(letter.getTransformula());
			}
		}

		return new NestedRun<>(traceSchemeNestedWord, acceleratedTraceSchemeStates);
	}

	/**
	 * Accelerate nested loops first to increase reliability of interpolants.
	 *
	 * @param nestingLoophead
	 * @param nestedLoophead
	 */
	private void accelerateNestedLoops(final IcfgLocation nestingLoophead, final IcfgLocation nestedLoophead) {
		/*
		 * In case of multiple nested loops, accelerate the inner one first (maybe check for delay for that)
		 */
		if (!mNestedLoops.containsKey(nestedLoophead)) {
			return;
		}
		if (mNestingRelation.containsKey(nestedLoophead)) {
			accelerateNestedLoops(nestedLoophead, mNestingRelation.get(nestedLoophead));
		}
		final List<UnmodifiableTransFormula> nestedLoopTfs = mNestedLoopsTf.get(nestedLoophead);
		boolean accelerationFinishedCorrectly = false;
		final List<UnmodifiableTransFormula> accelerations = new ArrayList<>();
		for (final UnmodifiableTransFormula loopPath : nestedLoopTfs) {
			mLogger.debug("Starting acceleration of nested loop");
			final UnmodifiableTransFormula acceleratedLoopRelation =
					mAccelerator.accelerateLoop(loopPath, nestedLoophead, AccelerationMethod.FAST_UPR);
			if (!mAccelerator.accelerationFinishedCorrectly()) {
				mLogger.debug("No acceleration found");
				accelerationFinishedCorrectly = false;
				break;
			}
			accelerationFinishedCorrectly = true;
			Term t = mPredHelper.makeReflexive(acceleratedLoopRelation.getFormula(), acceleratedLoopRelation);
			t = PartialQuantifierElimination.tryToEliminate(mServices, mLogger, mScript, t, mSimplificationTechnique,
					XnfConversionTechnique.BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION);
			final UnmodifiableTransFormula tf = mPredHelper.normalizeTerm(t, acceleratedLoopRelation, true);
			mLogger.debug("Computed Acceleration: " + tf.getFormula().toStringDirect());
			accelerations.add(tf);
		}
		if (!accelerationFinishedCorrectly) {
			return;
		}
		final UnmodifiableTransFormula nestedAcceleration = TransFormulaUtils.parallelComposition(mLogger, mServices,
				mScript, null, false, XnfConversionTechnique.BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION,
				accelerations.toArray(new UnmodifiableTransFormula[accelerations.size()]));
		Set<List<L>> nestingLoop;
		if (mLoops.containsKey(nestingLoophead)) {
			nestingLoop = mLoops.get(nestingLoophead);
		} else {
			nestingLoop = mNestedLoops.get(nestingLoophead);
		}

		final Set<List<UnmodifiableTransFormula>> nestingLoopAccelerated = new HashSet<>();

		for (final List<L> nestingLoopPath : nestingLoop) {
			final List<UnmodifiableTransFormula> nestingLoopPathAccelerated = new ArrayList<>();
			for (int i = 0; i < nestingLoopPath.size(); i++) {
				if (nestingLoopPath.get(i).getSource() == nestedLoophead) {
					mLogger.debug("found nested loophead");
					nestingLoopPathAccelerated.add(nestedAcceleration);
					i = mLoopSize.get(nestedLoophead).getSecond();
				} else {
					nestingLoopPathAccelerated.add(nestingLoopPath.get(i).getTransformula());
				}
			}
			nestingLoopAccelerated.add(nestingLoopPathAccelerated);
		}
		mLoopsAsTf.put(nestingLoophead, nestingLoopAccelerated);
		mLogger.debug("Nested loops accelerated");
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
	public IPredicate[] getInterpolants() {
		return mInterpolants;
	}

	@Override
	public Map<Integer, IPredicate> getPendingContexts() {
		return Collections.emptyMap();
	}

	@Override
	public IPredicate getPostcondition() {
		return mPredUnifier.getFalsePredicate();
	}

	@Override
	public IPredicate getPrecondition() {
		return mPredUnifier.getTruePredicate();
	}

	@Override
	public IPredicateUnifier getPredicateUnifier() {
		return mPredUnifier;
	}

	@Override
	public IProgramExecution<L, Term> getRcfgProgramExecution() {
		if (mFeasibleProgramExecution == null) {
			mFeasibleProgramExecution = computeProgramExecution();
		}
		return mFeasibleProgramExecution;
	}

	@Override
	public IStatisticsDataProvider getStatistics() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public List<L> getTrace() {
		return mCounterexample;
	}

	@Override
	public TraceCheckReasonUnknown getTraceCheckReasonUnknown() {
		return mReasonUnknown;
	}

	@Override
	public LBool isCorrect() {
		return mIsTraceCorrect;
	}

	@Override
	public boolean isPerfectSequence() {
		return isCorrect() == LBool.UNSAT;
	}

	@Override
	public boolean providesRcfgProgramExecution() {
		return mIsTraceCorrect != LBool.SAT;
	}

	@Override
	public boolean wasTracecheckFinishedNormally() {
		return mTraceCheckFinishedNormally;
	}

}
