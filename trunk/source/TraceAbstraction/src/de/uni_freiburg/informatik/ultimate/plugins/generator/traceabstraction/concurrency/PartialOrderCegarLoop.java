/*
 * Copyright (C) 2020 Marcel Ebbinghaus
 * Copyright (C) 2020-2022 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2020-2022 University of Freiburg
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
import java.util.Collections;
import java.util.Comparator;
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
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.DeterminizeNwa;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.InformationStorage;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.PowersetDeterminizer;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.TotalizeNwa;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.UnionNwa;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.AcceptingRunSearchVisitor;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.CoveringOptimizationVisitor;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.CoveringOptimizationVisitor.CoveringMode;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.DeadEndOptimizingSearchVisitor;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.IDfsVisitor;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.IIndependenceRelation;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.SleepSetCoveringRelation;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.SleepSetVisitorSearch;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.WrapperVisitor;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.multireduction.CoinFlipBudget;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.multireduction.OptimisticBudget;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.multireduction.SleepMapReduction;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.multireduction.SleepMapReduction.IBudgetFunction;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IDeterminizeStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IIntersectionStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IUnionStateFactory;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.debugidentifiers.DebugIdentifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.IHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IMLPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.ISLPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.MLPredicateWithConjuncts;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateWithConjuncts;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.BetterLockstepOrder;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.LoopLockstepOrder.PredicateWithLastThread;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.PartialOrderMode;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.PartialOrderReductionFacade;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.SleepSetStateFactoryForRefinement.SleepPredicate;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.independence.IndependenceSettings.AbstractionType;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.singletracecheck.InterpolationTechnique;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.BasicCegarLoop;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.CegarLoopStatisticsDefinitions;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.PredicateFactoryRefinement;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interpolantautomata.transitionappender.AbstractInterpolantAutomaton;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interpolantautomata.transitionappender.DeterministicInterpolantAutomaton;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;
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
public class PartialOrderCegarLoop<L extends IIcfgTransition<?>>
		extends BasicCegarLoop<L, INwaOutgoingLetterAndTransitionProvider<L, IPredicate>> {
	private final PartialOrderMode mPartialOrderMode;
	private final InformationStorageFactory mFactory = new InformationStorageFactory();

	private final PartialOrderReductionFacade<L> mPOR;
	private final List<IRefinableIndependenceProvider<L>> mIndependenceProviders;

	private final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> mProgram;
	private INwaOutgoingLetterAndTransitionProvider<L, IPredicate> mItpAutomata;
	private final List<AbstractInterpolantAutomaton<L>> mAbstractItpAutomata = new LinkedList<>();

	private final boolean mSupportsDeadEnds;

	public PartialOrderCegarLoop(final DebugIdentifier name,
			final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> initialAbstraction,
			final IIcfg<IcfgLocation> rootNode, final CfgSmtToolkit csToolkit, final PredicateFactory predicateFactory,
			final TAPreferences taPrefs, final Set<IcfgLocation> errorLocs, final InterpolationTechnique interpolation,
			final IUltimateServiceProvider services,
			final List<IRefinableIndependenceProvider<L>> independenceProviders, final Class<L> transitionClazz,
			final PredicateFactoryRefinement stateFactoryForRefinement) {
		super(name, initialAbstraction, rootNode, csToolkit, predicateFactory, taPrefs, errorLocs, interpolation, false,
				Collections.emptySet(), services, transitionClazz, stateFactoryForRefinement);

		assert !mPref.applyOneShotPOR() : "Turn off one-shot partial order reduction when using this CEGAR loop.";

		mPartialOrderMode = mPref.getPartialOrderMode();
		if (mPref.applyOneShotLbe()) {
			boolean hasAbstraction = false;
			for (int i = 0; !hasAbstraction && i < mPref.getNumberOfIndependenceRelations(); ++i) {
				hasAbstraction |= mPref.porIndependenceSettings(i).getAbstractionType() != AbstractionType.NONE;
			}
			if (mPartialOrderMode.hasPersistentSets() || hasAbstraction) {
				throw new UnsupportedOperationException(
						"Soundness is currently not guaranteed for this CEGAR loop if one-shot LBE is turned on.");
			}
		}

		mIndependenceProviders = independenceProviders;

		// Setup management of abstraction levels and corresponding independence relations.
		final int numIndependenceRelations = mIndependenceProviders.size();
		mLogger.info("Running %s with %d independence relations.", PartialOrderCegarLoop.class.getSimpleName(),
				numIndependenceRelations);
		if (numIndependenceRelations > 1) {
			mLogger.warn("Attention: Unsuitable combinations of independence relations may be unsound!");
			mLogger.warn("Only combine independence relations if you are sure the combination is sound.");
		}
		for (final var provider : mIndependenceProviders) {
			provider.initialize();
		}

		final List<IIndependenceRelation<IPredicate, L>> relations = mIndependenceProviders.stream()
				.map(IRefinableIndependenceProvider::retrieveIndependence).collect(Collectors.toList());
		mPOR = new PartialOrderReductionFacade<>(services, predicateFactory, rootNode, errorLocs,
				mPref.getPartialOrderMode(), mPref.getDfsOrderType(), mPref.getDfsOrderSeed(), relations,
				this::makeBudget);

		// TODO support dead ends with the new structure
		mSupportsDeadEnds = false && mPref.getNumberOfIndependenceRelations() == 1
				&& mPref.porIndependenceSettings(0).getAbstractionType() == AbstractionType.NONE;

		mProgram = initialAbstraction;
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
		if (mItpAutomata == null) {
			mItpAutomata = determinized;
		} else {
			mItpAutomata = new UnionNwa<>(mItpAutomata, determinized, mFactory, false);
		}
		mAbstraction =
				new InformationStorage<>(mProgram == null ? mAbstraction : mProgram, mItpAutomata, mFactory, false);

		// update independence relations (in case of abstract independence)
		for (int i = 0; i < mIndependenceProviders.size(); ++i) {
			final var container = mIndependenceProviders.get(i);
			container.refine(mRefinementResult);
			mPOR.replaceIndependence(i, container.retrieveIndependence());
		}

		// TODO (Dominik 2020-12-17) Really implement this acceptance check (see BasicCegarLoop::refineAbstraction)
		return true;
	}

	@Override
	protected boolean isAbstractionEmpty() throws AutomataOperationCanceledException {
		switchToOnDemandConstructionMode();

		mCegarLoopBenchmark.start(CegarLoopStatisticsDefinitions.EmptinessCheckTime);
		try {
			final IDfsVisitor<L, IPredicate> visitor = createVisitor();
			mPOR.apply(mAbstraction, visitor);
			mCounterexample = getCounterexample(visitor);
			switchToReadonlyMode();

			assert mCounterexample == null || accepts(getServices(), mAbstraction, mCounterexample.getWord(),
					false) : "Counterexample is not accepted by abstraction";
			return mCounterexample == null;
		} finally {
			mCegarLoopBenchmark.stop(CegarLoopStatisticsDefinitions.EmptinessCheckTime);
		}
	}

	private IBudgetFunction<L, IPredicate> makeBudget(final SleepMapReduction<L, IPredicate, IPredicate> reduction) {
		final IBudgetFunction<L, IPredicate> budget = new OptimisticBudget<>(new AutomataLibraryServices(mServices),
				mPOR.getDfsOrder(), mPOR.getSleepMapFactory(), this::createVisitor, reduction);
		switch (mPref.useCoinflip()) {
		case OFF:
			return budget;
		case FALLBACK:
			return new CoinFlipBudget<>(true, mPref.coinflipSeed(), mPref.getCoinflipProbability(mIteration), budget);
		case PURE:
			return new CoinFlipBudget<>(true, mPref.coinflipSeed(), mPref.getCoinflipProbability(mIteration),
					(s, l) -> 1);
		}
		throw new IllegalArgumentException("Unknown coinflip mode: " + mPref.useCoinflip());
	}

	@Override
	public void finish() {
		for (final AbstractInterpolantAutomaton<L> ia : mAbstractItpAutomata) {
			mCegarLoopBenchmark.reportInterpolantAutomatonStates(ia.size());
		}
		mPOR.reportStatistics(Activator.PLUGIN_ID);

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

		if (PartialOrderReductionFacade.ENABLE_COVERING_OPTIMIZATION) {
			visitor = new CoveringOptimizationVisitor<>(visitor, new SleepSetCoveringRelation<>(mPOR.getSleepFactory()),
					CoveringMode.PRUNE);
		}

		if (mSupportsDeadEnds) {
			visitor = new DeadEndOptimizingSearchVisitor<>(visitor, mPOR.getDeadEndStore(), false);
		}

		return visitor;
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
		final boolean result = isFalseLiteral(state);
		return result;
	}

	public static boolean isFalseLiteral(final IPredicate state) {
		if (state instanceof PredicateWithConjuncts) {
			// By the way we create conjunctions in the state factory below, any conjunction that contains the conjunct
			// "false" will contain no other conjuncts.
			final ImmutableList<IPredicate> conjuncts = ((PredicateWithConjuncts) state).getConjuncts();
			return conjuncts.size() == 1 && isFalseLiteral(conjuncts.getHead());
		}

		// We assume here that all inconsistent interpolant predicates are syntactically equal to "false".
		return SmtUtils.isFalseLiteral(state.getFormula());
	}

	private static boolean isTrueLiteral(final IPredicate state) {
		if (state instanceof PredicateWithConjuncts) {
			final ImmutableList<IPredicate> conjuncts = ((PredicateWithConjuncts) state).getConjuncts();
			return conjuncts.size() == 1 && isTrueLiteral(conjuncts.getHead());
		}
		return SmtUtils.isTrueLiteral(state.getFormula());
	}

	public static ImmutableList<IPredicate> getConjuncts(final IPredicate conjunction) {
		if (conjunction == null) {
			return ImmutableList.empty();
		}
		if (conjunction instanceof PredicateWithConjuncts) {
			return ((PredicateWithConjuncts) conjunction).getConjuncts();
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

	@Override
	protected void constructErrorAutomaton() throws AutomataOperationCanceledException {
		throw new UnsupportedOperationException("Error automata not supported for " + PartialOrderCegarLoop.class);
	}

	@Override
	protected void computeIcfgHoareAnnotation() {
		throw new UnsupportedOperationException("Hoare annotation not supported for " + PartialOrderCegarLoop.class);
	}

	private final class InformationStorageFactory
			implements IIntersectionStateFactory<IPredicate>, IUnionStateFactory<IPredicate> {
		@Override
		public IPredicate createEmptyStackState() {
			return mStateFactoryForRefinement.createEmptyStackState();
		}

		@Override
		public IPredicate intersection(final IPredicate state1, final IPredicate state2) {
			final IPredicate newState;
			// if (isFalseLiteral(state2)) {
			newState = mPredicateFactory.construct(id -> new MLPredicateWithConjuncts(id,
					((IMLPredicate) state1).getProgramPoints(), getConjuncts(state2)));
			// } else {
			// newState = mPredicateFactory
			// .construct(id -> new MLPredicateWithConjuncts(id, (IMLPredicate) state1, state2));
			// }

			// TODO support dead ends with the new structure
			// if (mSupportsDeadEnds) {
			// mPOR.getDeadEndStore().copyDeadEndInformation(state1, newState);
			// }

			return newState;
		}

		@Override
		public IPredicate createSinkStateContent() {
			throw new UnsupportedOperationException();
		}

		// TODO If the new structure helps as much as expected, the optimizations in this method may be unnecessary.
		// TODO Evaluate and possibly remove.
		@Override
		public IPredicate union(final IPredicate state1, final IPredicate state2) {
			final IPredicate newState;
			if (isFalseLiteral(state1) || isTrueLiteral(state2)) {
				// If state1 is "false", we add no other conjuncts.
				// Similarly, there is no point in adding state2 as conjunct if it is "true".
				if (state1 instanceof PredicateWithConjuncts) {
					final var conjState1 = (PredicateWithConjuncts) state1;
					newState = mPredicateFactory
							.construct(id -> new PredicateWithConjuncts(id, conjState1.getConjuncts()));
				} else {
					newState = mPredicateFactory
							.construct(id -> new PredicateWithConjuncts(id, ImmutableList.singleton(state1)));
				}
			} else if (isFalseLiteral(state2) || isTrueLiteral(state1)) {
				// If state2 is "false", we ignore all previous conjuncts. This allows us to optimize in #isFalseLiteral
				// As another (less important) optimization, we also ignore state1 if it is "true".
				newState = mPredicateFactory
						.construct(id -> new PredicateWithConjuncts(id, ImmutableList.singleton(state2)));
			} else {
				// In the normal case, we simply add state2 as conjunct.
				newState = mPredicateFactory.construct(id -> new PredicateWithConjuncts(id, state1, state2));
			}

			// TODO support dead ends with the new structure
			// if (mSupportsDeadEnds) {
			// mPOR.getDeadEndStore().copyDeadEndInformation(state1, newState);
			// }

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
			final List<IPredicate> conjuncts = down2up.get(createEmptyStackState())
					// sort predicates to ensure deterministic order
					.stream().sorted(Comparator.comparingInt(Object::hashCode)).collect(Collectors.toList());

			// Interpolant automaton should not have "don't care".
			assert conjuncts.stream().noneMatch(mPredicateFactory::isDontCare);

			// Don't create unnecessary conjunctions of single predicates.
			if (conjuncts.size() == 1) {
				return DataStructureUtils.getOneAndOnly(conjuncts, "predicate");
			}

			return mPredicateFactory.and(conjuncts);
		}
	}
}
