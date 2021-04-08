/*
 * Copyright (C) 2020 Marcel Ebbinghaus
 * Copyright (C) 2020 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2020 University of Freiburg
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
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
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
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.concurrency;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.IRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.InformationStorage;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.TotalizeNwa;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.AcceptingRunSearchVisitor;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.CachedIndependenceRelation;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.CachedIndependenceRelation.IIndependenceCache;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.CachedPersistentSetChoice;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.ConditionTransformingIndependenceRelation;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.ConstantDfsOrder;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.DeadEndOptimizingSearchVisitor;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.DefaultIndependenceCache;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.DepthFirstTraversal;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.IDfsOrder;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.IDfsVisitor;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.IIndependenceRelation;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.IPersistentSetChoice;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.PersistentSetReduction;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.SleepSetDelayReduction;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.SleepSetNewStateReduction;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.SleepSetVisitorSearch;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.UnionIndependenceRelation;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IIntersectionStateFactory;
import de.uni_freiburg.informatik.ultimate.core.lib.results.StatisticsResult;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.debugidentifiers.DebugIdentifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.IHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IMLPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.ISLPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.scripttransfer.TermTransferrer;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.solverbuilder.SolverBuilder;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.solverbuilder.SolverBuilder.SolverMode;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.solverbuilder.SolverBuilder.SolverSettings;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.singletracecheck.InterpolationTechnique;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.BasicCegarLoop;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.CegarLoopStatisticsDefinitions;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.independencerelation.DistributingIndependenceRelation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.independencerelation.SemanticConditionEliminator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.independencerelation.SemanticIndependenceRelation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.independencerelation.SyntacticIndependenceRelation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.independencerelation.ThreadSeparatingIndependenceRelation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interpolantautomata.transitionappender.AbstractInterpolantAutomaton;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.petrinetlbe.PetriNetLargeBlockEncoding.IPLBECompositionFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.util.statistics.StatisticsData;

/**
 * A CEGAR loop for concurrent programs, based on finite automata, which uses Partial Order Reduction (POR) in every
 * iteration to improve efficiency.
 *
 * @author Marcel Ebbinghaus
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 *
 * @param <L>
 *            The type of statements in the program.
 */
public class PartialOrderCegarLoop<L extends IIcfgTransition<?>> extends BasicCegarLoop<L> {
	private final PartialOrderMode mPartialOrderMode;
	private final IIntersectionStateFactory<IPredicate> mFactory;
	private final IDfsVisitor<L, IPredicate> mVisitor;
	private final IDfsOrder<L, IPredicate> mDfsOrder = ConstantDfsOrder.byHashCode();

	// Maps an IPredicate built through refinement rounds to the sequence of conjuncts it was built from.
	// This is used to distribute an independence query across conjuncts.
	private final Map<IPredicate, IPredicate[]> mPredicateConjuncts = new HashMap<>();

	// The list of independence relations to which independence queries for the different conjuncts of an IPredicate are
	// distributed. In every iteration, a relation is appended to deal with the additional conjunct.
	private final List<IIndependenceRelation<IPredicate, L>> mConjunctIndependenceRelations = new ArrayList<>();

	private final IIndependenceRelation<IPredicate, L> mIndependenceRelation;
	private final IIndependenceRelation<IPredicate, L> mConditionalRelation;
	private final IPersistentSetChoice<L, IPredicate> mPersistent;

	private final List<AbstractInterpolantAutomaton<L>> mAbstractItpAutomata = new LinkedList<>();

	public PartialOrderCegarLoop(final DebugIdentifier name, final IIcfg<IcfgLocation> rootNode,
			final CfgSmtToolkit csToolkit, final PredicateFactory predicateFactory, final TAPreferences taPrefs,
			final Collection<IcfgLocation> errorLocs, final InterpolationTechnique interpolation,
			final boolean computeHoareAnnotation, final IUltimateServiceProvider services,
			final IPLBECompositionFactory<L> compositionFactory, final Class<L> transitionClazz) {
		super(name, rootNode, csToolkit, predicateFactory, taPrefs, errorLocs, interpolation, computeHoareAnnotation,
				services, compositionFactory, transitionClazz);
		mPartialOrderMode = mPref.getPartialOrderMode();
		mFactory = new InformationStorageFactory();
		mVisitor = supportsDeadStateOptimization(mPartialOrderMode)
				? new DeadEndOptimizingSearchVisitor<>(this::createVisitor)
				: null;

		final IIndependenceRelation<IPredicate, L> semanticIndependence = constructSemanticIndependence(csToolkit);
		final DefaultIndependenceCache<IPredicate, L> independenceCache = new DefaultIndependenceCache<>();
		final IIndependenceRelation<IPredicate, L> unconditionalRelation =
				constructUnconditionalIndependence(semanticIndependence, independenceCache);
		mConditionalRelation = constructConditionalIndependence(semanticIndependence, independenceCache);
		mIndependenceRelation = constructIndependenceRelation(unconditionalRelation);
		mPersistent = createPersistentSets(unconditionalRelation);
	}

	// Turn off one-shot partial order reduction before initial iteration.
	@Override
	protected INwaOutgoingLetterAndTransitionProvider<L, IPredicate> computePartialOrderReduction(
			final PartialOrderMode mode, final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> input) {
		return input;
	}

	@Override
	protected boolean refineAbstraction() throws AutomataLibraryException {
		// Compute the enhanced interpolant automaton
		final IPredicateUnifier predicateUnifier = mRefinementEngine.getPredicateUnifier();
		final IHoareTripleChecker htc = getHoareTripleChecker();
		final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> ia = enhanceInterpolantAutomaton(
				mPref.interpolantAutomatonEnhancement(), predicateUnifier, htc, mInterpolAutomaton);
		if (ia instanceof AbstractInterpolantAutomaton<?>) {
			final AbstractInterpolantAutomaton<L> aia = (AbstractInterpolantAutomaton<L>) ia;
			aia.switchToReadonlyMode();
			mAbstractItpAutomata.add(aia);
		} else {
			mCegarLoopBenchmark.reportInterpolantAutomatonStates(ia.size());
		}

		// Automaton must be total and deterministic
		final TotalizeNwa<L, IPredicate> totalInterpol = new TotalizeNwa<>(ia, mStateFactoryForRefinement, true);
		assert !totalInterpol.nonDeterminismInInputDetected() : "interpolant automaton was nondeterministic";

		// Actual refinement step
		final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> oldAbstraction =
				(INwaOutgoingLetterAndTransitionProvider<L, IPredicate>) mAbstraction;
		mAbstraction = new InformationStorage<>(oldAbstraction, totalInterpol, mFactory, false);

		// Update independence relation
		mConjunctIndependenceRelations.add(mConditionalRelation);

		// TODO (Dominik 2020-12-17) Really implement this acceptance check (see BasicCegarLoop::refineAbstraction)
		return true;
	}

	@Override
	protected boolean isAbstractionEmpty() throws AutomataOperationCanceledException {
		final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> abstraction =
				(INwaOutgoingLetterAndTransitionProvider<L, IPredicate>) mAbstraction;

		switchToOnDemandConstructionMode();
		mCegarLoopBenchmark.start(CegarLoopStatisticsDefinitions.PartialOrderReductionTime);
		final AutomataLibraryServices automataServices = new AutomataLibraryServices(mServices);
		final IDfsVisitor<L, IPredicate> visitor = getNewVisitor();
		try {
			switch (mPartialOrderMode) {
			case SLEEP_DELAY_SET:
				new SleepSetDelayReduction<>(automataServices, abstraction, mSleepSetStateFactory,
						mIndependenceRelation, mDfsOrder, visitor);
				break;
			case SLEEP_NEW_STATES:
				new SleepSetNewStateReduction<>(automataServices, abstraction, mSleepSetStateFactory,
						mIndependenceRelation, mDfsOrder, visitor);
				break;
			case PERSISTENT_SETS:
				PersistentSetReduction.applyWithoutSleepSets(abstraction, mDfsOrder, mPersistent, visitor);
				break;
			case PERSISTENT_SLEEP_DELAY_SET:
				PersistentSetReduction.applyDelaySetReduction(automataServices, abstraction, mIndependenceRelation,
						mDfsOrder, mPersistent, visitor);
				break;
			case NONE:
				new DepthFirstTraversal<>(abstraction, mDfsOrder, visitor);
				break;
			default:
				throw new UnsupportedOperationException("Unsupported POR mode: " + mPartialOrderMode);
			}
			mCounterexample = getCounterexample(visitor);
			switchToReadonlyMode();
			return mCounterexample == null;
		} finally {
			mCegarLoopBenchmark.stop(CegarLoopStatisticsDefinitions.PartialOrderReductionTime);
		}
	}

	@Override
	public void finish() {
		for (final AbstractInterpolantAutomaton<L> ia : mAbstractItpAutomata) {
			mCegarLoopBenchmark.reportInterpolantAutomatonStates(ia.size());
		}

		final StatisticsData data = new StatisticsData();
		data.aggregateBenchmarkData(mIndependenceRelation.getStatistics());
		mServices.getResultService().reportResult(Activator.PLUGIN_ID,
				new StatisticsResult<>(Activator.PLUGIN_NAME, "Independence relation benchmarks", data));

		super.finish();
	}

	private IDfsVisitor<L, IPredicate> getNewVisitor() {
		if (mVisitor instanceof DeadEndOptimizingSearchVisitor<?, ?, ?>) {
			((DeadEndOptimizingSearchVisitor<?, ?, ?>) mVisitor).reset();
			return mVisitor;
		}
		return createVisitor();
	}

	private IRun<L, IPredicate> getCounterexample(IDfsVisitor<L, IPredicate> visitor) {
		if (visitor instanceof DeadEndOptimizingSearchVisitor<?, ?, ?>) {
			visitor = ((DeadEndOptimizingSearchVisitor<?, ?, IDfsVisitor<L, IPredicate>>) visitor).getUnderlying();
		}

		if (mPartialOrderMode == PartialOrderMode.PERSISTENT_SETS || mPartialOrderMode == PartialOrderMode.NONE) {
			return ((AcceptingRunSearchVisitor<L, IPredicate>) visitor).getAcceptingRun();
		}
		return ((SleepSetVisitorSearch<L, IPredicate>) visitor).constructRun();
	}

	private IDfsVisitor<L, IPredicate> createVisitor() {
		// TODO Refactor sleep set reductions to full DFS and always use (simpler) AcceptingRunSearchVisitor
		if (mPartialOrderMode == PartialOrderMode.PERSISTENT_SETS || mPartialOrderMode == PartialOrderMode.NONE) {
			return new AcceptingRunSearchVisitor<>(this::isGoalState, PartialOrderCegarLoop::isFalseState);
		}
		return new SleepSetVisitorSearch<>(this::isGoalState, PartialOrderCegarLoop::isFalseState);
	}

	private static final boolean supportsDeadStateOptimization(final PartialOrderMode mode) {
		// At the moment, only sleep sets with new states support this optimization.
		return mode == PartialOrderMode.SLEEP_NEW_STATES || mode == PartialOrderMode.PERSISTENT_SLEEP_NEW_STATES
				|| mode == PartialOrderMode.NONE;
	}

	private IIndependenceRelation<IPredicate, L> constructSemanticIndependence(final CfgSmtToolkit csToolkit) {
		final ManagedScript independenceScript = constructIndependenceScript();
		final TermTransferrer independenceTransferrer =
				new TermTransferrer(csToolkit.getManagedScript().getScript(), independenceScript.getScript());
		return new SemanticIndependenceRelation<>(mServices, independenceScript, true, false, independenceTransferrer);
	}

	private IIndependenceRelation<IPredicate, L> constructConditionalIndependence(
			final IIndependenceRelation<IPredicate, L> semanticIndependence,
			final IIndependenceCache<IPredicate, L> independenceCache) {
		// Note: Soundness of the SemanticConditionEliminator depends on the fact that all inconsistent predicates are
		// syntactically equal to "false". Here, this is achieved by usage of DistributingIndependenceRelation: The only
		// predicates we use as conditions are the original interpolants (i.e., not conjunctions of them), where we
		// assume this constraint holds.
		return new SemanticConditionEliminator<>(
				new CachedIndependenceRelation<>(semanticIndependence, independenceCache),
				PartialOrderCegarLoop::isFalseState);
	}

	private IIndependenceRelation<IPredicate, L> constructUnconditionalIndependence(
			final IIndependenceRelation<IPredicate, L> semanticIndependence,
			final IIndependenceCache<IPredicate, L> independenceCache) {
		return new CachedIndependenceRelation<>(
				new UnionIndependenceRelation<>(Arrays.asList(new SyntacticIndependenceRelation<>(),
						ConditionTransformingIndependenceRelation.unconditional(semanticIndependence))),
				independenceCache);
	}

	private IIndependenceRelation<IPredicate, L>
			constructIndependenceRelation(final IIndependenceRelation<IPredicate, L> unconditionalRelation) {
		mConjunctIndependenceRelations.add(unconditionalRelation);
		return new ThreadSeparatingIndependenceRelation<>(
				new DistributingIndependenceRelation<>(mConjunctIndependenceRelations, this::getConjuncts));
	}

	private final IPersistentSetChoice<L, IPredicate>
			createPersistentSets(final IIndependenceRelation<IPredicate, L> independence) {
		switch (mPartialOrderMode) {
		case PERSISTENT_SETS:
		case PERSISTENT_SLEEP_DELAY_SET:
			return (IPersistentSetChoice<L, IPredicate>) new CachedPersistentSetChoice<>(new ThreadBasedPersistentSets(
					mServices, mIcfg, (IIndependenceRelation<IPredicate, IcfgEdge>) independence));
		case NONE:
		case SLEEP_DELAY_SET:
		case SLEEP_NEW_STATES:
			return null;
		default:
			throw new UnsupportedOperationException("unsupported POR mode");
		}
	}

	private void switchToOnDemandConstructionMode() {
		for (final AbstractInterpolantAutomaton<L> aut : mAbstractItpAutomata) {
			aut.switchToOnDemandConstructionMode();
		}
	}

	private void switchToReadonlyMode() {
		for (final AbstractInterpolantAutomaton<L> aut : mAbstractItpAutomata) {
			aut.switchToReadonlyMode();
		}
	}

	private Boolean isGoalState(final IPredicate state) {
		assert state instanceof IMLPredicate || state instanceof ISLPredicate : "unexpected type of predicate: "
				+ state.getClass();

		final IcfgLocation[] programPoints;
		if (state instanceof ISLPredicate) {
			programPoints = new IcfgLocation[] { ((ISLPredicate) state).getProgramPoint() };
		} else {
			programPoints = ((IMLPredicate) state).getProgramPoints();
		}
		final boolean isErrorState = Arrays.stream(programPoints).anyMatch(mErrorLocs::contains);
		return isErrorState && !isFalseState(state);
	}

	private static Boolean isFalseState(final IPredicate state) {
		// We assume here that all inconsistent interpolant predicates are syntactically equal to "false".
		return SmtUtils.isFalseLiteral(state.getFormula());
	}

	private IPredicate[] getConjuncts(final IPredicate conjunction) {
		if (conjunction == null) {
			return new IPredicate[mIteration + 1];
		}
		return mPredicateConjuncts.getOrDefault(conjunction, new IPredicate[] { conjunction });
	}

	private ManagedScript constructIndependenceScript() {
		final SolverSettings settings = SolverBuilder.constructSolverSettings()
				.setSolverMode(SolverMode.External_DefaultMode)
				.setUseExternalSolver(true, SolverBuilder.COMMAND_Z3_NO_TIMEOUT + " -t:1000", SolverBuilder.LOGIC_Z3);
		final Script solver = SolverBuilder.buildAndInitializeSolver(mServices, settings, "SemanticIndependence");
		return new ManagedScript(mServices, solver);
	}

	private final class InformationStorageFactory implements IIntersectionStateFactory<IPredicate> {
		@Override
		public IPredicate createEmptyStackState() {
			return mStateFactoryForRefinement.createEmptyStackState();
		}

		@Override
		public IPredicate intersection(final IPredicate state1, final IPredicate state2) {
			// Create the actual predicate
			final Term formula;
			if (mPredicateFactory.isDontCare(state1)) {
				formula = state2.getFormula();
			} else {
				formula = mPredicateFactory.and(state1, state2).getFormula();
			}
			final IcfgLocation[] locations = ((IMLPredicate) state1).getProgramPoints();
			final IPredicate newState = mPredicateFactory.newMLPredicate(locations, formula);

			// Update the map back to individual conjuncts
			final IPredicate[] oldDistribution = getConjuncts(state1);
			final IPredicate[] newDistribution = Arrays.copyOf(oldDistribution, oldDistribution.length + 1);
			newDistribution[newDistribution.length - 1] = state2;
			mPredicateConjuncts.put(newState, newDistribution);

			// Transfer dead state info
			if (mVisitor instanceof DeadEndOptimizingSearchVisitor<?, ?, ?>) {
				final var deadEndVisitor = (DeadEndOptimizingSearchVisitor<?, IPredicate, ?>) mVisitor;
				if (deadEndVisitor.isDeadEndState(state1)) {
					deadEndVisitor.addDeadEndState(newState);
				}
			}

			if (mPersistent instanceof CachedPersistentSetChoice<?, ?>) {
				final var cache = (CachedPersistentSetChoice<?, IPredicate>) mPersistent;
				cache.transferCachedInformation(state1, newState);
			}

			return newState;
		}
	}
}
