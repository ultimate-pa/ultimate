/*
 * Copyright (C) 2022 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2022 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.TreeMap;
import java.util.TreeSet;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.automata.IRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.core.lib.results.StatisticsResult;
import de.uni_freiburg.informatik.ultimate.core.model.models.Payload;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.translation.AtomicTraceElement;
import de.uni_freiburg.informatik.ultimate.core.model.translation.AtomicTraceElement.AtomicTraceElementBuilder;
import de.uni_freiburg.informatik.ultimate.core.model.translation.IProgramExecution;
import de.uni_freiburg.informatik.ultimate.core.model.translation.IProgramExecution.ProgramState;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.jordan.JordanLoopAcceleration;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.jordan.JordanLoopAcceleration.JordanLoopAccelerationResult;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.jordan.JordanLoopAcceleration.JordanLoopAccelerationResult.AccelerationStatus;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.jordan.JordanLoopAccelerationStatisticsGenerator;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IcfgProgramExecution;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdgeFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.interpolant.IInterpolatingTraceCheck;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.interpolant.InterpolantComputationStatus;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.interpolant.InterpolantComputationStatus.ItpErrorStatus;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.SPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.tracecheck.TraceCheckReasonUnknown;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.taskidentifier.TaskIdentifier;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.solverbuilder.SolverBuilder.ExternalSolver;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.solverbuilder.SolverBuilder.SolverMode;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.solverbuilder.SolverBuilder.SolverSettings;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.singletracecheck.InterpolationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.singletracecheck.TraceCheckSpWp;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.singletracecheck.TraceCheckUtils;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.TaCheckAndRefinementPreferences;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashTreeRelation;
import de.uni_freiburg.informatik.ultimate.util.statistics.IStatisticsDataProvider;
import de.uni_freiburg.informatik.ultimate.util.statistics.StatisticsData;

/**
 * TraceCheck which applies loop acceleration to some loops in the trace.
 */
public class AcceleratedTraceCheck<L extends IIcfgTransition<?>> implements IInterpolatingTraceCheck<L> {

	private final ILogger mLogger;
	private final ManagedScript mMgdScript;
	private final IUltimateServiceProvider mServices;
	private final NestedRun<L, IPredicate> mCounterexample;
	private final IPredicate mPrecondition;
	private final IPredicate mPostcondition;
	private final IPredicateUnifier mPredicateUnifier;
	private final TaCheckAndRefinementPreferences mPrefs;
	private final IIcfg<?> mIcfg;
	private LBool mIsTraceCorrect;
	private IPredicate[] mInterpolants;
	private IProgramExecution<L, Term> mFeasibleProgramExecution;
	private TraceCheckReasonUnknown mReasonUnknown;
	private boolean mTraceCheckFinishedNormally;
	private final PredicateFactory mPredicateFactory;

	public AcceleratedTraceCheck(final IUltimateServiceProvider services, final ILogger logger,
			final TaCheckAndRefinementPreferences<L> prefs, final ManagedScript script,
			final IPredicateUnifier predicateUnifier, final IRun<L, IPredicate> counterexample,
			final IPredicate precondition, final IPredicate postcondition, final PredicateFactory predicateFactory) {
		mLogger = logger;
		mMgdScript = script;
		mServices = services;
		mCounterexample = (NestedRun<L, IPredicate>) counterexample;
		mPrecondition = precondition;
		mPostcondition = postcondition;
		mPrefs = prefs;
		mPredicateFactory = predicateFactory;

		mIcfg = mPrefs.getIcfgContainer();
		mPredicateUnifier = predicateUnifier;
		mInterpolants = null;

		final TreeMap<Integer, AcceleratedSegment> acceleratedSegments = constructAcceleratedSegments(mServices,
				mLogger, script, counterexample);
		if (acceleratedSegments.isEmpty()) {

			final TraceCheckSpWp<L> tc = checkTrace(mPrecondition, mPostcondition, mCounterexample);
			mIsTraceCorrect = tc.isCorrect();
			switch (tc.isCorrect()) {
			case SAT:
				mFeasibleProgramExecution = tc.getRcfgProgramExecution();
				break;
			case UNKNOWN:
				mReasonUnknown = tc.getTraceCheckReasonUnknown();
				break;
			case UNSAT:
				mInterpolants = tc.getForwardIpp().getPredicates().toArray(new IPredicate[0]);
				break;
			default:
				throw new AssertionError();
			}
		} else {
			final NestedRun<L, IPredicate> acceleratedCounterexample = construtAcceleratedCounterexample(mServices,
					mLogger, mMgdScript, mIcfg.getCfgSmtToolkit().getIcfgEdgeFactory(), acceleratedSegments,
					mCounterexample);
			final TraceCheckSpWp<L> tc = checkTrace(mPrecondition, mPostcondition, acceleratedCounterexample);
			mIsTraceCorrect = tc.isCorrect();
			switch (tc.isCorrect()) {
			case SAT:
				final IcfgProgramExecution<L> pe = tc.getRcfgProgramExecution();
				mFeasibleProgramExecution = constructProgramExecution(mCounterexample.getWord(), acceleratedSegments,
						pe);
				break;
			case UNKNOWN:
				mReasonUnknown = tc.getTraceCheckReasonUnknown();
				break;
			case UNSAT:
				mInterpolants = constructInterpolants(mCounterexample, acceleratedSegments, tc.getForwardPredicates());
				break;
			default:
				throw new AssertionError();
			}
		}
	}

	private IPredicate[] constructInterpolants(final NestedRun<L, IPredicate> counterexample,
			final TreeMap<Integer, AcceleratedSegment> acceleratedSegments,
			final List<IPredicate> interpolantsForAcceleratedTrace) {
		// Note that the i-th state comes before the i-th letter and the i-th
		// interpolant comes after the i-th letter
		final List<IPredicate> result = new ArrayList<>();
		int offset = 0;
		for (final Entry<Integer, AcceleratedSegment> entry : acceleratedSegments.entrySet()) {
			// While processing the trace we are now before the letter at position
			// `result.size()`
			final AcceleratedSegment aseg = entry.getValue();
			assert entry.getKey() == entry.getValue().getStartPosition();
			// Interpolants since last loop, including the last loop's postcondition and the
			// next loop's precondition
			final List<IPredicate> intermediateInterpolants = interpolantsForAcceleratedTrace
					.subList(result.size() - offset, aseg.getStartPosition() - offset);
			result.addAll(intermediateInterpolants);
			assert result.size() == aseg.getStartPosition();
			final IPredicate precondition = interpolantsForAcceleratedTrace.get(aseg.getStartPosition() - offset - 1);
			final IPredicate postcondition = interpolantsForAcceleratedTrace.get(aseg.getStartPosition() - offset);
			// Run for the trace from the first letter (inclusive) to the last letter
			// (inclusive) of the loop body
			final NestedRun<L, IPredicate> subRun = counterexample.getSubRun(aseg.getStartPosition(),
					aseg.getEndPosition() + 1);
			final TraceCheckSpWp<L> inter = checkTrace(precondition, postcondition, subRun);
			if (inter.isCorrect() != LBool.UNSAT) {
				throw new UnsupportedOperationException("Body trace check " + inter.isCorrect());
			}
			result.addAll(inter.getForwardPredicates());
			// So far we accumulate all interpolants before the last letter of the current
			// loop
			assert result.size() == aseg.getEndPosition();
			// we have to increase the offset by the number of newly added interpolants
			offset += (aseg.getEndPosition() - aseg.getStartPosition());
		}
		// finally, we have to add all remaining interpolants starting from the
		// postcondition of the last loop
		result.addAll(interpolantsForAcceleratedTrace.subList(result.size() - offset,
				interpolantsForAcceleratedTrace.size()));
		assert counterexample.getLength() == result.size() + 2;
		assert interpolantsForAcceleratedTrace.size() + offset == result.size();
		return result.toArray(new IPredicate[result.size()]);
	}

	private TraceCheckSpWp<L> checkTrace(final IPredicate precondition, final IPredicate postcondition,
			final NestedRun<L, IPredicate> counterexample) {
		final TraceCheckSpWp<L> tc = new TraceCheckSpWp<L>(precondition, postcondition,
				new TreeMap<Integer, IPredicate>(), NestedWord.nestedWord(counterexample.getWord()),
				mPrefs.getCfgSmtToolkit(), mPrefs.getAssertCodeBlockOrder(), mPrefs.getUnsatCores(),
				mPrefs.getUseLiveVariables(), mServices, mPrefs.computeCounterexample(), mPredicateFactory,
				mPredicateUnifier, InterpolationTechnique.ForwardPredicates, constructManagedScript(),
				XnfConversionTechnique.BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION, SimplificationTechnique.SIMPLIFY_DDA,
				TraceCheckUtils.getSequenceOfProgramPoints(NestedWord.nestedWord(counterexample.getWord())),
				mPrefs.collectInterpolantStatistics());
		return tc;
	}

	private ManagedScript constructManagedScript() {

		final long timeout = 12_000;
		final SolverSettings solverSettings = mPrefs.constructSolverSettings(new TaskIdentifier(null) {

			@Override
			protected String getSubtaskIdentifier() {
				return "TODO";
			}
		}).setUseExternalSolver(ExternalSolver.Z3, timeout).setSolverMode(SolverMode.External_ModelsAndUnsatCoreMode);
		return createExternalManagedScript(solverSettings);
	}

	protected ManagedScript createExternalManagedScript(final SolverSettings solverSettings) {
		return mPrefs.getIcfgContainer().getCfgSmtToolkit().createFreshManagedScript(mServices, solverSettings,
				"ChecksDuringAccel");
	}

	private IProgramExecution<L, Term> constructProgramExecution(final NestedWord<L> trace,
			final TreeMap<Integer, AcceleratedSegment> acceleratedSegments, final IcfgProgramExecution<L> pe) {
		final List<AtomicTraceElement<L>> ateList = new ArrayList<>();
		final Map<Integer, ProgramState<Term>> partialProgramStateMapping = new HashMap<>();
		final Map<TermVariable, Boolean>[] branchEncoders = new Map[trace.length()];
		final ProgramState<Term> initState = pe.getInitialProgramState();
		partialProgramStateMapping.put(-1, initState);
		boolean inAcceleratedSegment = false;
		int lastPosOfSegment = -1;
		int currentOffset = 0;
		for (int i = 0; i < trace.length(); i++) {
			if (acceleratedSegments.containsKey(i)) {
				inAcceleratedSegment = true;
				final AcceleratedSegment segment = acceleratedSegments.get(i);
				lastPosOfSegment = segment.getEndPosition();
				currentOffset += (segment.getEndPosition() - segment.getStartPosition());
			}
			if (inAcceleratedSegment) {
				final AtomicTraceElementBuilder<L> ateb = new AtomicTraceElementBuilder<>();
				ateb.setStepAndElement(trace.getSymbol(i));
				final AtomicTraceElement<L> ate = ateb.build();
				ateList.add(ate);
			} else {
				ateList.add(pe.getTraceElement(i - currentOffset));
				final ProgramState<Term> ps = pe.getProgramState(i - currentOffset);
				if (ps != null) {
					partialProgramStateMapping.put(i, ps);
				}
				final Map<TermVariable, Boolean> be = pe.getBranchEncoders()[i - currentOffset];
				if (be != null) {
					branchEncoders[i] = be;
				}
			}
			if (i == lastPosOfSegment) {
				inAcceleratedSegment = false;
			}
		}
		return new IcfgProgramExecution<L>(ateList, partialProgramStateMapping, branchEncoders, pe.isConcurrent(),
				(Class<L>) pe.getTraceElementClass());
	}

	private NestedRun<L, IPredicate> construtAcceleratedCounterexample(final IUltimateServiceProvider services,
			final ILogger logger, final ManagedScript mgdScript, final IcfgEdgeFactory icfgEdgeFactory,
			final TreeMap<Integer, AcceleratedSegment> acceleratedSegments,
			final NestedRun<L, IPredicate> counterexample) {
		int lastcut = 0;
		NestedWord<L> currentWord = new NestedWord<>();
		final ArrayList<IPredicate> currentSequenceofStates = new ArrayList<>();
		for (final Entry<Integer, AcceleratedSegment> entry : acceleratedSegments.entrySet()) {
			final AcceleratedSegment accelSegment = entry.getValue();
			final NestedWord<L> subwordBefore = counterexample.getWord().getSubWord(lastcut,
					accelSegment.getStartPosition());
			currentWord = currentWord.concatenate(subwordBefore);
			final List<IPredicate> sequenceOfStatesBefore = counterexample.getStateSequence().subList(lastcut,
					entry.getKey());
			currentSequenceofStates.addAll(sequenceOfStatesBefore);
			final SPredicate loopPredicate = (SPredicate) counterexample
					.getStateAtPosition(accelSegment.getStartPosition());
			final IIcfgTransition<?> accelerationEdge = icfgEdgeFactory.createInternalTransition(
					loopPredicate.getProgramPoint(), loopPredicate.getProgramPoint(), new Payload(),
					accelSegment.getTransitiveClosure());
			final L l = (L) accelerationEdge;
			final NestedWord<L> singleWord = new NestedWord<L>(l, NestedWord.INTERNAL_POSITION);
			currentWord = currentWord.concatenate(singleWord);
			currentSequenceofStates.add(loopPredicate);
			lastcut = accelSegment.getEndPosition() + 1;
		}
		final NestedWord<L> tailWord = counterexample.getWord().getSubWord(lastcut, counterexample.getLength() - 1);
		currentWord = currentWord.concatenate(tailWord);
		currentSequenceofStates.addAll(counterexample.getStateSequence().subList(lastcut, counterexample.getLength()));
		return new NestedRun<L, IPredicate>(currentWord, currentSequenceofStates);
	}

	private TreeMap<Integer, AcceleratedSegment> constructAcceleratedSegments(final IUltimateServiceProvider services,
			final ILogger logger, final ManagedScript mgdScript, final IRun<L, IPredicate> counterexample) {
		final TreeMap<Integer, AcceleratedSegment> result = new TreeMap<>();
		final HashTreeRelation<IcfgLocation, Integer> similarProgramPoints = findSimilarProgramPoints(
				counterexample.getStateSequence());
		for (int i = 0; i < counterexample.getLength(); i++) {
			final IcfgLocation currentProgramPoint = ((SPredicate) counterexample.getStateSequence().get(i))
					.getProgramPoint();
			final TreeSet<Integer> positionsWithSimilarProgramPoint = similarProgramPoints
					.getImage(currentProgramPoint);
			final Integer nextPosition = positionsWithSimilarProgramPoint.higher(i);
			if (nextPosition != null) {
				final NestedWord<L> nestedWord = (NestedWord<L>) counterexample.getWord();
				final NestedWord<L> subWord = nestedWord.getSubWord(i, nextPosition);
				final UnmodifiableTransFormula transitiveClosure = accelerate(services, logger, mgdScript, subWord);
				if (transitiveClosure != null) {
					result.put(i, new AcceleratedSegment(i, nextPosition - 1, transitiveClosure));
					i = nextPosition - 1;
				}
			}
		}
		return result;
	}

	private UnmodifiableTransFormula accelerate(final IUltimateServiceProvider services, final ILogger logger,
			final ManagedScript mgdScript, final NestedWord<L> subWord) {
		if (!subWord.hasEmptyNestingRelation()) {
			return null;
		}
		final List<UnmodifiableTransFormula> transformulas = subWord.asList().stream().map(L::getTransformula)
				.collect(Collectors.toList());
		final UnmodifiableTransFormula sequentialComposition = TransFormulaUtils.sequentialComposition(logger, services,
				mgdScript, true, true, false, XnfConversionTechnique.BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION,
				SimplificationTechnique.SIMPLIFY_DDA, transformulas);
		final JordanLoopAccelerationResult jla = JordanLoopAcceleration.accelerateLoop(mServices, mMgdScript,
				sequentialComposition, true);
		final JordanLoopAccelerationStatisticsGenerator stat = jla.getJordanLoopAccelerationStatistics();
		final StatisticsData stats = new StatisticsData();
		stats.aggregateBenchmarkData(stat);
		services.getResultService().reportResult(Activator.PLUGIN_ID,
				new StatisticsResult<>(Activator.PLUGIN_NAME, "LoopAccelerationStatistics", stats));
		if (jla.getAccelerationStatus() != AccelerationStatus.SUCCESS) {
			throw new UnsupportedOperationException(JordanLoopAcceleration.UNSUPPORTED_PREFIX + " "
					+ jla.getAccelerationStatus() + " " + jla.getErrorMessage());
		}
		return jla.getTransFormula();
	}

	private static HashTreeRelation<IcfgLocation, Integer> findSimilarProgramPoints(
			final List<IPredicate> programPoints) {
		final HashTreeRelation<IcfgLocation, Integer> result = new HashTreeRelation<>();
		for (int i = 0; i < programPoints.size(); i++) {
			final SPredicate pred = (SPredicate) programPoints.get(i);
			final IcfgLocation programPoint = pred.getProgramPoint();
			result.addPair(programPoint, i);
		}
		return result;
	}

	@Override
	public InterpolantComputationStatus getInterpolantComputationStatus() {
		if (isCorrect() == LBool.UNSAT) {
			return new InterpolantComputationStatus();
		}
		if (isCorrect() == LBool.SAT) {
			return new InterpolantComputationStatus(ItpErrorStatus.TRACE_FEASIBLE, null);
		}
		throw new UnsupportedOperationException();
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
		return mPostcondition;
	}

	@Override
	public IPredicate getPrecondition() {
		return mPrecondition;
	}

	@Override
	public IPredicateUnifier getPredicateUnifier() {
		return mPredicateUnifier;
	}

	@Override
	public IProgramExecution<L, Term> getRcfgProgramExecution() {
		if (mFeasibleProgramExecution == null) {
			throw new AssertionError();
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
		return mCounterexample.getWord().asList();
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
		return mIsTraceCorrect == LBool.SAT;
	}

	@Override
	public boolean wasTracecheckFinishedNormally() {
		return mTraceCheckFinishedNormally;
	}

	private static class AcceleratedSegment {
		final int mStartPosition;
		final int mEndPosition;
		final UnmodifiableTransFormula mTransitiveClosure;

		public AcceleratedSegment(final int startPosition, final int endPosition,
				final UnmodifiableTransFormula transitiveClosure) {
			super();
			mStartPosition = startPosition;
			mEndPosition = endPosition;
			mTransitiveClosure = transitiveClosure;
		}

		public int getStartPosition() {
			return mStartPosition;
		}

		public int getEndPosition() {
			return mEndPosition;
		}

		public UnmodifiableTransFormula getTransitiveClosure() {
			return mTransitiveClosure;
		}

	}

}
