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
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.IRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.translation.IProgramExecution;
import de.uni_freiburg.informatik.ultimate.lib.acceleratedinterpolation.Interpolator.InterpolationMethod;
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
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula.Infeasibility;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.PartialQuantifierElimination;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SolverBuilder;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SolverBuilder.SolverMode;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SolverBuilder.SolverSettings;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.Substitution;
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
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.singletracecheck.TraceCheckUtils;
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
	private final LBool mIsTraceCorrect;
	private IPredicate[] mInterpolants;
	private IProgramExecution<IIcfgTransition<IcfgLocation>, Term> mFeasibleProgramExecution;
	private final TraceCheckReasonUnknown mReasonUnknown;
	private final boolean mTraceCheckFinishedNormally;
	private final IIcfgSymbolTable mSymbolTable;

	private final Map<IcfgLocation, Set<List<LETTER>>> mLoops;
	private final Map<IcfgLocation, LETTER> mLoopExitTransitions;
	private final Map<IcfgLocation, Pair<Integer, Integer>> mLoopSize;
	private final Map<IcfgLocation, Set<UnmodifiableTransFormula>> mAccelerations;
	private final Accelerator<LETTER> mAccelerator;
	private final Loopdetector<LETTER> mLoopdetector;

	public AcceleratedInterpolation(final ILogger logger, final ITraceCheckPreferences prefs,
			final ManagedScript script, final IPredicateUnifier predicateUnifier,
			final IRun<LETTER, IPredicate> counterexample) {
		mLogger = logger;
		mScript = script;
		mServices = prefs.getUltimateServices();
		mCounterexampleTrace = counterexample;
		mCounterexample = mCounterexampleTrace.getWord().asList();
		mPrefs = prefs;
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
		mLoopdetector = new Loopdetector<>(mCounterexample, mLogger);
		mPredTransformer = new PredicateTransformer<>(mScript, new TermDomainOperationProvider(mServices, mScript));

		mPredHelper = new PredicateHelper<>(mPredUnifier, mPredTransformer, mLogger, mScript, mServices);
		mCounterexampleTf = mPredHelper.traceToListOfTfs(mCounterexample);

		// TODO give a better reason
		mReasonUnknown = null;
		mTraceCheckFinishedNormally = true;

		/*
		 * Find loops in the trace.
		 */
		mLoops = mLoopdetector.getLoops();
		mLoopExitTransitions = mLoopdetector.getLoopExitTransitions();
		mLoopSize = mLoopdetector.getLoopSize();

		/*
		 * After finding loops in the trace, start calculating loop accelerations.
		 */
		for (final Entry<IcfgLocation, Set<List<LETTER>>> loophead : mLoops.entrySet()) {
			final Set<UnmodifiableTransFormula> accelerations = new HashSet<>();
			for (final List<LETTER> loop : loophead.getValue()) {
				final UnmodifiableTransFormula loopRelation = mPredHelper.traceToTf(loop);

				final UnmodifiableTransFormula acceleratedLoopRelation =
						mAccelerator.accelerateLoop(loopRelation, AccelerationMethod.NONE);

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
			mAccelerations.put(loophead.getKey(), accelerations);
		}

		// TODO: DD 2020-05-07: It might be necessary to create a fresh mScript instance for the interpolation, in
		// particular if you want to interpolate multiple times. Hence, I added constructManagedScriptForInterpolation()
		// -- but perhaps you want to re-use the script from CfgSmtScript
		final ManagedScript ipScript = constructManagedScriptForInterpolation();
		final Interpolator<LETTER> interpolator =
				new Interpolator<>(mPredUnifier, mPredTransformer, mLogger, ipScript, mServices, mPredHelper, mPrefs);

		if (mLoops.isEmpty()) {
			mLogger.debug("No loops found in this trace.");
			interpolator.generateInterpolants(InterpolationMethod.CRAIG_NESTED, mCounterexampleTrace, null);
			mIsTraceCorrect = interpolator.isTraceCorrect();
			if (mIsTraceCorrect == LBool.UNSAT) {
				mInterpolants = interpolator.getInterpolants();
			}
			return;
		}

		// TODO: DD 2020-05-07: Do not "just" generate a list of UnmodifiableTransFormula, but a
		// IRun<IAction,IPredicate>. Use mCounterexample to get the IPredicates.
		final NestedRun<LETTER, IPredicate> traceScheme = generateMetaTrace();

		interpolator.generateInterpolants(InterpolationMethod.CRAIG_NESTED, mCounterexampleTrace, mAccelerations);
		mIsTraceCorrect = interpolator.isTraceCorrect();
		if (mIsTraceCorrect == LBool.UNSAT) {
			mInterpolants = interpolator.getInterpolants();
		}
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
	 * Transform the counterexample to a meta trace by "pulling" loopheads into two locations.
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

			if (!mLoops.containsKey(l.getTarget())) {
				continue;
			}

			final Set<List<LETTER>> loopTrace = new HashSet<>(mLoops.get(l.getTarget()));
			final UnmodifiableTransFormula[] tfs =
					new UnmodifiableTransFormula[mAccelerations.get(l.getTarget()).size()];
			int j = 0;
			for (final UnmodifiableTransFormula tf : mAccelerations.get(l.getTarget())) {
				counterExampleAccelerated.add(tf);
				tfs[j] = tf;
				j++;
			}

			final PredicateFactory predFactory = new PredicateFactory(mServices, mScript, mSymbolTable);

			final UnmodifiableTransFormula loopAcceleration = TransFormulaUtils.parallelComposition(mLogger, mServices,
					0, mScript, null, false, XnfConversionTechnique.BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION, tfs);

			final LETTER loopExitTransition = mLoopExitTransitions.get(l.getTarget());
			final IcfgLocation loopExitLocation = loopExitTransition.getTarget();

			final StringDebugIdentifier newExitId =
					new StringDebugIdentifier(loopExitLocation.getDebugIdentifier().toString() + "_primed");

			final IcfgLocation newExitLocation = new IcfgLocation(newExitId, loopExitLocation.getProcedure());

			final LETTER acceleratedTransition = (LETTER) mIcfgEdgeFactory.createInternalTransition(l.getTarget(),
					newExitLocation, l.getTarget().getPayload(), loopAcceleration);
			final LETTER newLoopExitTransition = (LETTER) mIcfgEdgeFactory.createInternalTransition(newExitLocation,
					loopExitLocation, loopExitLocation.getPayload(), loopExitTransition.getTransformula());

			counterExampleAcceleratedLetter.add(acceleratedTransition);
			counterExampleAcceleratedLetter.add(newLoopExitTransition);

			final Term acceleratedTransitionDefaultVars = normalizeTerm(loopAcceleration);
			final Term newExitTransitionDefaultVars = normalizeTerm(loopExitTransition.getTransformula());

			final SPredicate acceleratedSPred =
					predFactory.newSPredicate(newExitLocation, acceleratedTransitionDefaultVars);
			final SPredicate newExitSPred = predFactory.newSPredicate(loopExitLocation, newExitTransitionDefaultVars);

			acceleratedTraceSchemeStates.add(traceStates.get(i + 1));
			acceleratedTraceSchemeStates.add(acceleratedSPred);
			// acceleratedTraceSchemeStates.add(newExitSPred);
			// counterExampleAccelerated.add(loopExitTransition.getTransformula());
			final Pair<Integer, Integer> loopSize = mLoopSize.get(l.getTarget());
			i = loopSize.getSecond();
		}

		acceleratedTraceSchemeStates.add(traceStates.get(counterExampleNonAccelerated.size()));

		final NestedWord<LETTER> traceSchemeNestedWord = TraceCheckUtils.toNestedWord(counterExampleAcceleratedLetter);
		final NestedRun<LETTER, IPredicate> traceSchemeRun =
				new NestedRun<>(traceSchemeNestedWord, acceleratedTraceSchemeStates);
		return traceSchemeRun;
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

	/**
	 * replace variables in term with its default termvariables, needed for {@link IPredicate} creation
	 *
	 * @param t
	 * @return
	 */
	private Term normalizeTerm(final UnmodifiableTransFormula t) {
		final HashMap<Term, Term> subMap = new HashMap<>();
		final Term tTerm = t.getFormula();

		final Map<IProgramVar, TermVariable> inVars = new HashMap<>();
		final Map<IProgramVar, TermVariable> outVars = new HashMap<>();

		for (final Entry<IProgramVar, TermVariable> outVar : t.getOutVars().entrySet()) {
			subMap.put(outVar.getValue(), outVar.getKey().getTermVariable());
			outVars.put(outVar.getKey(), outVar.getKey().getTermVariable());
		}
		for (final Entry<IProgramVar, TermVariable> inVar : t.getInVars().entrySet()) {
			subMap.put(inVar.getValue(), inVar.getKey().getTermVariable());
			inVars.put(inVar.getKey(), inVar.getKey().getTermVariable());
		}
		final Substitution sub = new Substitution(mScript, subMap);
		final Term newTerm = sub.transform(tTerm);
		return newTerm;
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
