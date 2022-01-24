package de.uni_freiburg.informatik.ultimate.lib.acceleratedinterpolation;

import java.util.ArrayList;
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
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.acceleratedinterpolation.Interpolator.InterpolationMethod;
import de.uni_freiburg.informatik.ultimate.lib.acceleratedinterpolation.MetaTraceTransformer.MetaTraceApplicationMethod;
import de.uni_freiburg.informatik.ultimate.lib.acceleratedinterpolation.loopaccelerator.IAccelerator;
import de.uni_freiburg.informatik.ultimate.lib.acceleratedinterpolation.loopdetector.ILoopdetector;
import de.uni_freiburg.informatik.ultimate.lib.acceleratedinterpolation.looppreprocessor.ILoopPreprocessor;
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
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateTransformer;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.SPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.TermDomainOperationProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.tracecheck.ITraceCheckPreferences;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.quantifier.PartialQuantifierElimination;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.solverbuilder.SolverBuilder;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.solverbuilder.SolverBuilder.SolverMode;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.solverbuilder.SolverBuilder.SolverSettings;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.singletracecheck.TraceCheckUtils;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

public class AcceleratedInterpolationCore<L extends IIcfgTransition<?>> {

	/**
	 * Indicate if the loop acceleration is bounded (-> precise: only one acceleration per loop), or unbounded (->
	 * underapproximation: multiple accelerations per loop)
	 */
	public enum AccelerationApproximationType {
		PRECISE, UNDERAPPROXIMATION
	}

	private final ILogger mLogger;
	private final ManagedScript mScript;
	private final IAccelerator mAccelerator;
	private final ILoopdetector<IcfgLocation, L> mLoopdetector;
	private final ILoopPreprocessor<IcfgLocation, L, UnmodifiableTransFormula> mLoopPreprocessor;
	private final PredicateHelper<L> mPredHelper;
	private final IUltimateServiceProvider mServices;
	private final IPredicateUnifier mPredUnifier;
	private final PredicateTransformer<Term, IPredicate, TransFormula> mPredTransformer;
	private final SimplificationTechnique mSimplificationTechnique;
	private final ITraceCheckPreferences mPrefs;
	private final IIcfg<? extends IcfgLocation> mIcfg;
	private final IcfgEdgeFactory mIcfgEdgeFactory;
	private IPredicate[] mInterpolants;
	// private IProgramExecution<L, Term> mFeasibleProgramExecution;
	private final IIcfgSymbolTable mSymbolTable;
	private final IRun<L, IPredicate> mCounterexampleTrace;
	private final List<L> mCounterexample;
	private final List<UnmodifiableTransFormula> mCounterexampleTf;

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
	private AccelerationApproximationType mApproximationType;
	private final MetaTraceApplicationMethod mMetaTraceApplicationMethod;
	private final MetaTraceTransformer<L> mMetaTraceTransformer;

	public AcceleratedInterpolationCore(final IUltimateServiceProvider services, final ILogger logger,
			final ManagedScript script, final IPredicateUnifier predicateUnifier, final ITraceCheckPreferences prefs,
			final IRun<L, IPredicate> counterexample, final IIcfg<?> icfg,
			final ILoopdetector<IcfgLocation, L> loopdetector,
			final ILoopPreprocessor<IcfgLocation, L, UnmodifiableTransFormula> loopPreprocessor,
			final IAccelerator accelerator) {

		mScript = script;
		mLogger = logger;
		mIcfg = icfg;
		mCounterexampleTrace = counterexample;
		mCounterexample = counterexample.getWord().asList();
		mLoopdetector = loopdetector;
		mAccelerator = accelerator;
		mAccelerations = new HashMap<>();
		mLoopPreprocessor = loopPreprocessor;
		mLoops = mLoopdetector.getLoops();
		mLoopsAsTf = mLoopdetector.getLoopsTf();
		mNestedLoopsAsTf = mLoopdetector.getNestedLoopsTf();
		mNestingRelation = mLoopdetector.getNestingRelation();
		mNestedLoops = mLoopdetector.getNestedLoops();
		mLoopSize = mLoopdetector.getLoopSize();
		mLoopExitTransitions = mLoopdetector.getLoopExitTransitions();
		mNestedLoopsTf = new HashMap<>();
		mSymbolTable = mIcfg.getCfgSmtToolkit().getSymbolTable();

		mPrefs = prefs;
		mServices = services;
		mPredUnifier = predicateUnifier;
		mPredTransformer = new PredicateTransformer<>(mScript, new TermDomainOperationProvider(mServices, mScript));
		mSimplificationTechnique = prefs.getSimplificationTechnique();

		mApproximationType = AccelerationApproximationType.PRECISE;
		mMetaTraceApplicationMethod = MetaTraceApplicationMethod.ONLY_AT_FIRST_LOOP_ENTRY;

		mIcfgEdgeFactory = mIcfg.getCfgSmtToolkit().getIcfgEdgeFactory();

		mPredHelper = new PredicateHelper<>(mPredUnifier, mPredTransformer, mLogger, mScript, mServices);
		mMetaTraceTransformer = new MetaTraceTransformer<>(mLogger, mScript, mCounterexample, mPredUnifier, mServices,
				mPredTransformer, mIcfg.getCfgSmtToolkit());
		mCounterexampleTf = mPredHelper.traceToListOfTfs(mCounterexample);

		mInterpolants = new IPredicate[mCounterexample.size()];
		mInterpolants[0] = mPredUnifier.getTruePredicate();
		mInterpolants[mCounterexample.size() - 1] = mPredUnifier.getFalsePredicate();
	}

	/**
	 * Main function of accelInterpol
	 */
	public LBool acceleratedInterpolationCoreIsCorrect() {
		/*
		 * After finding loops in the trace, start calculating loop accelerations.
		 */

		if (!mNestedLoops.isEmpty()) {
			final Map<IcfgLocation, Set<List<L>>> nestedLoopFiltered = new HashMap<>(mNestedLoops);
			for (final Entry<IcfgLocation, Set<List<L>>> nestedLoop : nestedLoopFiltered.entrySet()) {
				if (nestedLoop.getValue() == null) {
					mNestedLoops.remove(nestedLoop.getKey());
					continue;
				}
			}
			if (mLoopPreprocessor != null) {
				mNestedLoopsTf = mLoopPreprocessor.preProcessLoop(mNestedLoops);
			}
			for (final Entry<IcfgLocation, IcfgLocation> nesting : mNestingRelation.entrySet()) {
				accelerateNestedLoops(nesting.getKey(), nesting.getValue());
			}
		}

		if (mLoopPreprocessor != null) {
			mLoopsTf = mLoopPreprocessor.preProcessLoopInterprocedual(mLoops);
			mLogger.debug("Done Preprocessing");
		}

		final Iterator<Entry<IcfgLocation, Set<List<L>>>> loopheadIterator = mLoops.entrySet().iterator();
		while (loopheadIterator.hasNext()) {
			final Entry<IcfgLocation, Set<List<L>>> loophead = loopheadIterator.next();
			final List<UnmodifiableTransFormula> loopTf = mLoopsTf.get(loophead.getKey());
			boolean accelerationFinishedCorrectly = false;
			final List<UnmodifiableTransFormula> accelerations = new ArrayList<>();
			for (final UnmodifiableTransFormula loop : loopTf) {
				mLogger.debug("Starting acceleration");
				final UnmodifiableTransFormula acceleratedLoopRelation =
						mAccelerator.accelerateLoop(loop, loophead.getKey());
				if (!mAccelerator.accelerationFinishedCorrectly()) {
					mLogger.debug("No acceleration found");
					accelerationFinishedCorrectly = false;
					break;
				}
				accelerationFinishedCorrectly = true;
				final Term t = mPredHelper.makeReflexive(acceleratedLoopRelation.getFormula(), acceleratedLoopRelation);
				// t = PartialQuantifierElimination.eliminateCompat(mServices, mScript, mSimplificationTechnique, term);
				final UnmodifiableTransFormula tf = mPredHelper.normalizeTerm(t, acceleratedLoopRelation, false);

				if (mLogger.isDebugEnabled()) {
					mLogger.debug("Computed Acceleration: " + tf.getFormula().toStringDirect());
					mLogger.debug("Simplified: " + SmtUtils
							.simplify(mScript, tf.getFormula(), mServices, SimplificationTechnique.SIMPLIFY_DDA)
							.toStringDirect());
				}

				accelerations.add(tf);
			}
			if (!accelerationFinishedCorrectly) {
				loopheadIterator.remove();
				break;
			}
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
					mLogger.debug(SmtUtils.simplify(mScript, metaTrace.getSymbol(i).getTransformula().getFormula(),
							mServices, SimplificationTechnique.SIMPLIFY_DDA).toStringDirect());
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

	private IPredicate[] refineMetaInterpolants(final IPredicate[] unrefinedMetaInterpolants,
			final NestedRun<L, IPredicate> metaTrace) {

		final IPredicate[] result = new IPredicate[unrefinedMetaInterpolants.length];
		final List<L> metaTraceTransitions = metaTrace.getWord().asList();
		for (int i = 0; i < metaTrace.getLength() - 2; i++) {
			final IPredicate metaInterpolant;
			if (i == 0) {
				metaInterpolant = mPredUnifier.getTruePredicate();
			} else {
				metaInterpolant = unrefinedMetaInterpolants[i - 1];
			}
			final UnmodifiableTransFormula transition = metaTraceTransitions.get(i).getTransformula();
			final Term inductiveInterpolant = mPredTransformer.strongestPostcondition(metaInterpolant, transition);
			result[i] = mPredUnifier.getOrConstructPredicate(inductiveInterpolant);
		}
		return result;
	}

	/**
	 * Constructs a Transformula where every variable is unchanged.
	 *
	 * @param tf
	 * @return
	 */
	private UnmodifiableTransFormula constructEpsilon() {
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
		return mPrefs.getIcfgContainer().getCfgSmtToolkit().createFreshManagedScript(mServices, solverSettings);
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
					mAccelerator.accelerateLoop(loopPath, nestedLoophead);
			if (!mAccelerator.accelerationFinishedCorrectly()) {
				mLogger.debug("No acceleration found");
				accelerationFinishedCorrectly = false;
				break;
			}
			accelerationFinishedCorrectly = true;
			Term t = mPredHelper.makeReflexive(acceleratedLoopRelation.getFormula(), acceleratedLoopRelation);
			final Term term = t;
			t = PartialQuantifierElimination.eliminateCompat(mServices, mScript, mSimplificationTechnique, term);
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

	public IPredicate[] getInterpolants() {
		return mInterpolants;
	}
}
