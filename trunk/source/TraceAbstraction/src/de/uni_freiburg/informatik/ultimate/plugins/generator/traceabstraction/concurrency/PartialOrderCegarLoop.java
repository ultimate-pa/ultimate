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

import java.util.Arrays;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.IRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.DeterminizeNwa;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.InformationStorage;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.PowersetDeterminizer;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.TotalizeNwa;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.AcceptingRunSearchVisitor;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.CoveringOptimizationVisitor;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.CoveringOptimizationVisitor.CoveringMode;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.DeadEndOptimizingSearchVisitor;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.IDfsVisitor;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.IIndependenceRelation;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.SleepSetVisitorSearch;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.WrapperVisitor;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IDeterminizeStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IIntersectionStateFactory;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IcfgUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdgeIterator;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.debugidentifiers.DebugIdentifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.IHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IMLPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.ISLPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.MLPredicateWithConjuncts;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.tracehandling.IRefinementEngineResult;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.solverbuilder.SolverBuilder;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.solverbuilder.SolverBuilder.ExternalSolver;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.solverbuilder.SolverBuilder.SolverMode;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.solverbuilder.SolverBuilder.SolverSettings;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.singletracecheck.InterpolationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckutils.independencerelation.IndependenceBuilder;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckutils.independencerelation.abstraction.ICopyActionFactory;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckutils.independencerelation.abstraction.IRefinableAbstraction;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckutils.independencerelation.abstraction.RefinableCachedAbstraction;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckutils.independencerelation.abstraction.SpecificVariableAbstraction;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckutils.independencerelation.abstraction.VariableAbstraction;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckutils.petrinetlbe.PetriNetLargeBlockEncoding.IPLBECompositionFactory;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.BasicCegarLoop;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.CegarLoopStatisticsDefinitions;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.concurrency.LoopLockstepOrder.PredicateWithLastThread;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.concurrency.SleepSetStateFactoryForRefinement.SleepPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interpolantautomata.transitionappender.AbstractInterpolantAutomaton;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interpolantautomata.transitionappender.DeterministicInterpolantAutomaton;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences.InterpolantAutomatonEnhancement;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ImmutableList;

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
	// Turn on to prune sleep set states where same program state with smaller sleep set already explored.
	public static final boolean ENABLE_COVERING_OPTIMIZATION = false;

	private final PartialOrderMode mPartialOrderMode;
	private final IIntersectionStateFactory<IPredicate> mFactory = new InformationStorageFactory();
	private final PartialOrderReductionFacade<L> mPOR;
	private final IRefinableIndependenceContainer<L> mIndependenceContainer;

	private final List<AbstractInterpolantAutomaton<L>> mAbstractItpAutomata = new LinkedList<>();

	public PartialOrderCegarLoop(final DebugIdentifier name, final IIcfg<IcfgLocation> rootNode,
			final CfgSmtToolkit csToolkit, final PredicateFactory predicateFactory, final TAPreferences taPrefs,
			final Set<IcfgLocation> errorLocs, final InterpolationTechnique interpolation,
			final boolean computeHoareAnnotation, final IUltimateServiceProvider services,
			final IPLBECompositionFactory<L> compositionFactory, final ICopyActionFactory<L> copyFactory,
			final Class<L> transitionClazz) {
		super(name, rootNode, csToolkit, predicateFactory, taPrefs, errorLocs, interpolation, computeHoareAnnotation,
				services, compositionFactory, transitionClazz);
		mPartialOrderMode = mPref.getPartialOrderMode();

		// Setup management of abstraction levels and corresponding independence relations.
		final IIndependenceRelation<IPredicate, L> independence = constructIndependence(csToolkit);
		final var letterAbstraction = constructAbstraction(copyFactory);
		if (letterAbstraction == null) {
			mIndependenceContainer = new StaticIndependenceContainer<>(independence);
		} else {
			mIndependenceContainer = new IndependenceContainerWithAbstraction<>(
					new RefinableCachedAbstraction<>(letterAbstraction), independence);
		}
		mIndependenceContainer.initialize();

		mPOR = new PartialOrderReductionFacade<>(services, predicateFactory, rootNode, errorLocs,
				mPref.getPartialOrderMode(), mPref.getDfsOrderType(), mPref.getDfsOrderSeed(),
				mIndependenceContainer.currentIndependence());
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
		final IPredicateUnifier predicateUnifier = mRefinementResult.getPredicateUnifier();
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
		final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> determinized;
		switch (mPref.interpolantAutomatonEnhancement()) {
		case PREDICATE_ABSTRACTION:
		case PREDICATE_ABSTRACTION_CANNIBALIZE:
		case PREDICATE_ABSTRACTION_CONSERVATIVE:
			// already total and deterministic
			assert ia instanceof DeterministicInterpolantAutomaton<?>;
			determinized = ia;
			break;
		case NONE:
			// make automaton total
			final IPredicate initialSink = DataStructureUtils.getOneAndOnly(ia.getInitialStates(), "initial state");
			assert initialSink == predicateUnifier.getTruePredicate() : "initial state should be TRUE";
			final TotalizeNwa<L, IPredicate> totalInterpol = new TotalizeNwa<>(ia, initialSink, false);

			// determinize total automaton
			final var det = new PowersetDeterminizer<>(totalInterpol, false, new DeterminizationFactory());
			determinized = new DeterminizeNwa<>(new AutomataLibraryServices(mServices), totalInterpol, det,
					mStateFactoryForRefinement, null, false);
			break;
		default:
			throw new UnsupportedOperationException("PartialOrderCegarLoop currently does not support enhancement "
					+ mPref.interpolantAutomatonEnhancement());
		}

		// Actual refinement step
		final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> oldAbstraction =
				(INwaOutgoingLetterAndTransitionProvider<L, IPredicate>) mAbstraction;
		mAbstraction = new InformationStorage<>(oldAbstraction, determinized, mFactory, false);

		// update independence in case of abstract independence
		mIndependenceContainer.refine(mRefinementResult);
		mPOR.replaceIndependence(mIndependenceContainer.currentIndependence());

		// TODO (Dominik 2020-12-17) Really implement this acceptance check (see BasicCegarLoop::refineAbstraction)
		return true;
	}

	@Override
	protected boolean isAbstractionEmpty() throws AutomataOperationCanceledException {
		final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> abstraction =
				(INwaOutgoingLetterAndTransitionProvider<L, IPredicate>) mAbstraction;

		switchToOnDemandConstructionMode();
		mCegarLoopBenchmark.start(CegarLoopStatisticsDefinitions.PartialOrderReductionTime);
		final IDfsVisitor<L, IPredicate> visitor = createVisitor();
		try {
			mPOR.apply(abstraction, visitor);
			mCounterexample = getCounterexample(visitor);
			switchToReadonlyMode();

			assert mCounterexample == null || accepts(getServices(), abstraction, mCounterexample.getWord(),
					false) : "Counterexample is not accepted by abstraction";
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
		mPOR.reportStatistics();
		super.finish();
	}

	private IRun<L, IPredicate> getCounterexample(IDfsVisitor<L, IPredicate> visitor) {
		if (visitor instanceof WrapperVisitor<?, ?, ?>) {
			visitor = ((WrapperVisitor<L, IPredicate, IDfsVisitor<L, IPredicate>>) visitor).getBaseVisitor();
		}
		if (mPartialOrderMode.hasSleepSets() && !mPartialOrderMode.doesUnrolling()) {
			// TODO Refactor sleep set reductions to full DFS and always use (simpler) AcceptingRunSearchVisitor
			return ((SleepSetVisitorSearch<L, IPredicate>) visitor).constructRun();
		}
		return ((AcceptingRunSearchVisitor<L, IPredicate>) visitor).getAcceptingRun();
	}

	private IDfsVisitor<L, IPredicate> createVisitor() {
		IDfsVisitor<L, IPredicate> visitor;
		if (mPartialOrderMode.hasSleepSets() && !mPartialOrderMode.doesUnrolling()) {
			// TODO Refactor sleep set reductions to full DFS and always use (simpler) AcceptingRunSearchVisitor
			// TODO once this is done, we can also give a more precise return type and avoid casts in getCounterexample
			visitor = new SleepSetVisitorSearch<>(this::isGoalState, this::isProvenState);
		} else {
			visitor = new AcceptingRunSearchVisitor<>(this::isGoalState, this::isProvenState);
		}
		if (mPOR.getDfsOrder() instanceof BetterLockstepOrder<?, ?>) {
			visitor = ((BetterLockstepOrder<L, IPredicate>) mPOR.getDfsOrder()).wrapVisitor(visitor);
		}

		if (ENABLE_COVERING_OPTIMIZATION) {
			visitor = new CoveringOptimizationVisitor<>(visitor,
					new SleepSetStateFactoryForRefinement.FactoryCoveringRelation<>(
							(SleepSetStateFactoryForRefinement<L>) mPOR.getSleepFactory()),
					CoveringMode.PRUNE);
		}
		return new DeadEndOptimizingSearchVisitor<>(visitor, mPOR.getDeadEndStore(), false);
	}

	private IIndependenceRelation<IPredicate, L> constructIndependence(final CfgSmtToolkit csToolkit) {
		return IndependenceBuilder
				// Semantic independence forms the base.
				.<L> semantic(getServices(), constructIndependenceScript(), csToolkit.getManagedScript().getScript(),
						mPref.getConditionalPor(), mPref.getSymmetricPor())
				// Add syntactic independence check (cheaper sufficient condition).
				.withSyntacticCheck()
				// Cache independence query results.
				.cached()
				// Setup condition optimization (if conditional independence is enabled).
				// =========================================================================
				// NOTE: Soundness of the condition elimination here depends on the fact that all inconsistent
				// predicates are syntactically equal to "false". Here, this is achieved by usage of
				// #withDisjunctivePredicates: The only predicates we use as conditions are the original interpolants
				// (i.e., not conjunctions of them), where we assume this constraint holds.
				.withConditionElimination(PartialOrderCegarLoop::isFalseLiteral)
				// We ignore "don't care" conditions stemming from the initial program automaton states.
				.withFilteredConditions(p -> !mPredicateFactory.isDontCare(p))
				.withDisjunctivePredicates(PartialOrderCegarLoop::getConjuncts)
				// =========================================================================
				// Never consider letters of the same thread to be independent.
				.threadSeparated()
				// Retrieve the constructed relation.
				.build();
	}

	private ManagedScript constructIndependenceScript() {
		final SolverSettings settings = SolverBuilder.constructSolverSettings()
				.setSolverMode(SolverMode.External_DefaultMode).setUseExternalSolver(ExternalSolver.Z3, 1000);
		final Script solver = SolverBuilder.buildAndInitializeSolver(getServices(), settings, "SemanticIndependence");
		return new ManagedScript(getServices(), solver);
	}

	private IRefinableAbstraction<NestedWordAutomaton<L, IPredicate>, ?, L>
			constructAbstraction(final ICopyActionFactory<L> copyFactory) {
		final Set<IProgramVar> allVariables = IcfgUtils.collectAllProgramVars(mCsToolkit);
		switch (mPref.getPorAbstraction()) {
		case VARIABLES_GLOBAL:
			return new VariableAbstraction<>(copyFactory, mCsToolkit.getManagedScript(), allVariables);
		case VARIABLES_LOCAL:
			if (mPref.interpolantAutomatonEnhancement() != InterpolantAutomatonEnhancement.NONE) {
				throw new UnsupportedOperationException(
						"specific variable abstraction is only supported with interpolant automaton enhancement turned off");
			}
			final Set<L> allLetters =
					new IcfgEdgeIterator(mIcfg).asStream().map(x -> (L) x).collect(Collectors.toSet());
			return new SpecificVariableAbstraction<>(copyFactory, mCsToolkit.getManagedScript(), allVariables,
					allLetters);
		case NONE:
			return null;
		default:
			throw new UnsupportedOperationException("Unknown abstraction type: " + mPref.getPorAbstraction());
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

	private boolean isGoalState(final IPredicate state) {
		assert state instanceof IMLPredicate || state instanceof ISLPredicate : "unexpected type of predicate: "
				+ state.getClass();

		final boolean isErrorState;
		if (state instanceof ISLPredicate) {
			isErrorState = mErrorLocs.contains(((ISLPredicate) state).getProgramPoint());
		} else {
			isErrorState = Arrays.stream(((IMLPredicate) state).getProgramPoints()).anyMatch(mErrorLocs::contains);
		}
		return isErrorState && !isProvenState(state);
	}

	private boolean isProvenState(IPredicate state) {
		final PartialOrderReductionFacade.StateSplitter<IPredicate> splitter = mPOR.getStateSplitter();
		if (splitter != null) {
			state = splitter.getOriginal(state);
		}
		return isFalseLiteral(state);
	}

	private static boolean isFalseLiteral(final IPredicate state) {
		if (state instanceof MLPredicateWithConjuncts) {
			// By the way we create conjunctions in the state factory below, any conjunction that contains the conjunct
			// "false" will contain no other conjuncts.
			final ImmutableList<IPredicate> conjuncts = ((MLPredicateWithConjuncts) state).getConjuncts();
			return conjuncts.size() == 1 && isFalseLiteral(conjuncts.getHead());
		}

		// We assume here that all inconsistent interpolant predicates are syntactically equal to "false".
		return SmtUtils.isFalseLiteral(state.getFormula());
	}

	private static boolean isTrueLiteral(final IPredicate state) {
		if (state instanceof MLPredicateWithConjuncts) {
			final ImmutableList<IPredicate> conjuncts = ((MLPredicateWithConjuncts) state).getConjuncts();
			return conjuncts.size() == 1 && isTrueLiteral(conjuncts.getHead());
		}
		return SmtUtils.isTrueLiteral(state.getFormula());
	}

	private static List<IPredicate> getConjuncts(final IPredicate conjunction) {
		if (conjunction == null) {
			return ImmutableList.empty();
		}
		if (conjunction instanceof MLPredicateWithConjuncts) {
			return ((MLPredicateWithConjuncts) conjunction).getConjuncts();
		}

		// TODO use mPOR.mStateSplitter for this
		if (conjunction instanceof PredicateWithLastThread) {
			return getConjuncts(((PredicateWithLastThread) conjunction).getUnderlying());
		}
		if (conjunction instanceof SleepPredicate<?>) {
			return getConjuncts(((SleepPredicate<?>) conjunction).getUnderlying());
		}

		return ImmutableList.singleton(conjunction);
	}

	private final class InformationStorageFactory implements IIntersectionStateFactory<IPredicate> {
		@Override
		public IPredicate createEmptyStackState() {
			return mStateFactoryForRefinement.createEmptyStackState();
		}

		@Override
		public IPredicate intersection(final IPredicate state1, final IPredicate state2) {
			if (isFalseLiteral(state1) || isTrueLiteral(state2)) {
				// If state1 is "false", we add no other conjuncts, and do not create a new state.
				// Similarly, there is no point in adding state2 as conjunct if it is "true".
				return state1;
			}

			final IPredicate newState;
			if (isFalseLiteral(state2) || isTrueLiteral(state1)) {
				// If state2 is "false", we ignore all previous conjuncts. This allows us to optimize in #isFalseLiteral
				// As another (less important) optimization, we also ignore state1 if it is "true".
				newState = mPredicateFactory.construct(id -> new MLPredicateWithConjuncts(id,
						((IMLPredicate) state1).getProgramPoints(), ImmutableList.singleton(state2)));
			} else {
				// In the normal case, we simply add state2 as conjunct.
				newState = mPredicateFactory
						.construct(id -> new MLPredicateWithConjuncts(id, (IMLPredicate) state1, state2));
			}

			mPOR.getDeadEndStore().copyDeadEndInformation(state1, newState);
			return newState;
		}
	}

	private final class DeterminizationFactory implements IDeterminizeStateFactory<IPredicate> {
		@Override
		public IPredicate createEmptyStackState() {
			return mPredicateFactoryInterpolantAutomata.createEmptyStackState();
		}

		@Override
		public IPredicate determinize(final Map<IPredicate, Set<IPredicate>> down2up) {
			// No support for calls and returns means the map should always have a simple structure.
			assert down2up.size() == 1 && down2up.containsKey(createEmptyStackState());
			final Set<IPredicate> conjuncts = down2up.get(createEmptyStackState());

			// Interpolant automaton should not have "don't care".
			assert conjuncts.stream().noneMatch(mPredicateFactory::isDontCare);

			// Don't create unnecessary conjunctions of single predicates.
			if (conjuncts.size() == 1) {
				return DataStructureUtils.getOneAndOnly(conjuncts, "predicate");
			}

			return mPredicateFactory.and(conjuncts);
		}
	}

	/**
	 * Encapsulates management of abstraction levels and corresponding independence relations.
	 *
	 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
	 *
	 * @param <L>
	 *            The type of letters for which an independence relation is managed.
	 */
	private interface IRefinableIndependenceContainer<L extends IIcfgTransition<?>> {
		void initialize();

		void refine(IRefinementEngineResult<L, NestedWordAutomaton<L, IPredicate>> refinement);

		IIndependenceRelation<IPredicate, L> currentIndependence();
	}

	/**
	 * An {@link IRefinableIndependenceContainer} implementation for the case where we only consider concrete
	 * commutativity.
	 *
	 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
	 */
	private static class StaticIndependenceContainer<L extends IIcfgTransition<?>>
			implements IRefinableIndependenceContainer<L> {
		private final IIndependenceRelation<IPredicate, L> mIndependence;

		public StaticIndependenceContainer(final IIndependenceRelation<IPredicate, L> independence) {
			mIndependence = independence;
		}

		@Override
		public void initialize() {
			// nothing to initialize
		}

		@Override
		public void refine(final IRefinementEngineResult<L, NestedWordAutomaton<L, IPredicate>> refinement) {
			// nothing to refine
		}

		@Override
		public IIndependenceRelation<IPredicate, L> currentIndependence() {
			return mIndependence;
		}
	}

	/**
	 * An {@link IRefinableIndependenceContainer} implementation for the case where we consider abstract commutativity
	 * given by some refinable abstraction function.
	 *
	 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
	 *
	 * @param <H>
	 *            The type of abstraction levels
	 */
	private static class IndependenceContainerWithAbstraction<L extends IIcfgTransition<?>, H>
			implements IRefinableIndependenceContainer<L> {
		private final IRefinableAbstraction<NestedWordAutomaton<L, IPredicate>, H, L> mRefinableAbstraction;
		private final IIndependenceRelation<IPredicate, L> mUnderlyingIndependence;
		private H mAbstractionLevel;

		public IndependenceContainerWithAbstraction(
				final IRefinableAbstraction<NestedWordAutomaton<L, IPredicate>, H, L> abstraction,
				final IIndependenceRelation<IPredicate, L> underlyingIndependence) {
			mRefinableAbstraction = abstraction;
			mUnderlyingIndependence = underlyingIndependence;
		}

		@Override
		public void initialize() {
			mAbstractionLevel = mRefinableAbstraction.getInitial();
		}

		@Override
		public void refine(final IRefinementEngineResult<L, NestedWordAutomaton<L, IPredicate>> refinement) {
			final H newLevel = mRefinableAbstraction.refine(mAbstractionLevel, refinement);
			assert mRefinableAbstraction.getHierarchy().compare(newLevel, mAbstractionLevel)
					.isLessOrEqual() : "Refinement must yield a lower abstraction level";
			mAbstractionLevel = newLevel;
		}

		@Override
		public IIndependenceRelation<IPredicate, L> currentIndependence() {
			return IndependenceBuilder.fromPredicateActionIndependence(mUnderlyingIndependence)
					// Apply abstraction to each letter before checking commutativity.
					.withAbstraction(mRefinableAbstraction, mAbstractionLevel)
					// Retrieve the constructed relation.
					.build();
		}
	}
}
