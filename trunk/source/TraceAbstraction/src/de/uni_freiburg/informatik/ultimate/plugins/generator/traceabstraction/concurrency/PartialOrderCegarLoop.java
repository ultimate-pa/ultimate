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
import java.util.Collections;
import java.util.LinkedList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.IRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.InformationStorage;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.TotalizeNwa;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.AcceptingRunSearchVisitor;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.CachedIndependenceRelation.IIndependenceCache;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.CoveringOptimizationVisitor;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.CoveringOptimizationVisitor.CoveringMode;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.DeadEndOptimizingSearchVisitor;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.DefaultIndependenceCache;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.IDfsVisitor;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.IIndependenceRelation;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.SleepSetVisitorSearch;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.WrapperVisitor;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IIntersectionStateFactory;
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
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.solverbuilder.SolverBuilder;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.solverbuilder.SolverBuilder.SolverMode;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.solverbuilder.SolverBuilder.SolverSettings;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.singletracecheck.InterpolationTechnique;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.BasicCegarLoop;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.CegarLoopStatisticsDefinitions;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.independencerelation.DistributingIndependenceRelation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.independencerelation.IndependenceBuilder;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.independencerelation.ThreadSeparatingIndependenceRelation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interpolantautomata.transitionappender.AbstractInterpolantAutomaton;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.petrinetlbe.PetriNetLargeBlockEncoding.IPLBECompositionFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;
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
	private final boolean mConditionalPor;
	private final boolean mSymmetricPor;
	private final IIntersectionStateFactory<IPredicate> mFactory;
	private final IDfsVisitor<L, IPredicate> mVisitor;
	private final PartialOrderReductionFacade<L> mPOR;

	// The list of independence relations to which independence queries for the different conjuncts of an IPredicate are
	// distributed. In every iteration, a relation is appended to deal with the additional conjunct.
	private final List<IIndependenceRelation<IPredicate, L>> mConjunctIndependenceRelations = new ArrayList<>();

	private final IIndependenceRelation<IPredicate, L> mIndependenceRelation;
	private final IIndependenceRelation<IPredicate, L> mConditionalRelation;

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
		mVisitor = mPartialOrderMode.supportsDeadStateOptimization()
				? new DeadEndOptimizingSearchVisitor<>(this::createVisitor)
				: null;

		mConditionalPor = mPref.getConditionalPor();
		mSymmetricPor = mPref.getSymmetricPor();
		final IIndependenceRelation<IPredicate, L> semanticIndependence = constructSemanticIndependence(csToolkit);
		final DefaultIndependenceCache<IPredicate, L> independenceCache = new DefaultIndependenceCache<>();
		final IIndependenceRelation<IPredicate, L> unconditionalRelation =
				constructUnconditionalIndependence(semanticIndependence, independenceCache);
		if (mConditionalPor) {
			mConditionalRelation = constructConditionalIndependence(semanticIndependence, independenceCache);
		} else {
			mConditionalRelation = null;
		}
		mIndependenceRelation = constructIndependenceRelation(unconditionalRelation);

		mPOR = new PartialOrderReductionFacade<>(services, predicateFactory, rootNode, errorLocs,
				mPref.getPartialOrderMode(), mPref.getDfsOrderType(), mPref.getDfsOrderSeed(), mIndependenceRelation);
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
		if (mConditionalPor) {
			mConjunctIndependenceRelations.add(mConditionalRelation);
		}

		// TODO (Dominik 2020-12-17) Really implement this acceptance check (see BasicCegarLoop::refineAbstraction)
		return true;
	}

	@Override
	protected boolean isAbstractionEmpty() throws AutomataOperationCanceledException {
		final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> abstraction =
				(INwaOutgoingLetterAndTransitionProvider<L, IPredicate>) mAbstraction;

		switchToOnDemandConstructionMode();
		mCegarLoopBenchmark.start(CegarLoopStatisticsDefinitions.PartialOrderReductionTime);
		final IDfsVisitor<L, IPredicate> visitor = getNewVisitor();
		try {
			mPOR.apply(abstraction, visitor);
			mCounterexample = getCounterexample(visitor);
			switchToReadonlyMode();

			assert mCounterexample == null || accepts(mServices, abstraction, mCounterexample.getWord(),
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
		if (visitor instanceof WrapperVisitor<?, ?, ?>) {
			visitor = ((WrapperVisitor<L, IPredicate, ?>) visitor).getBaseVisitor();
		}

		if (mPartialOrderMode.hasSleepSets()) {
			// TODO Refactor sleep set reductions to full DFS and always use (simpler) AcceptingRunSearchVisitor
			return ((SleepSetVisitorSearch<L, IPredicate>) visitor).constructRun();
		}
		return ((AcceptingRunSearchVisitor<L, IPredicate>) visitor).getAcceptingRun();
	}

	private IDfsVisitor<L, IPredicate> createVisitor() {
		IDfsVisitor<L, IPredicate> visitor;
		if (mPartialOrderMode.hasSleepSets()) {
			// TODO Refactor sleep set reductions to full DFS and always use (simpler) AcceptingRunSearchVisitor
			visitor = new SleepSetVisitorSearch<>(this::isGoalState, PartialOrderCegarLoop::isProvenState);
		} else {
			visitor = new AcceptingRunSearchVisitor<>(this::isGoalState, PartialOrderCegarLoop::isProvenState);
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
		return visitor;
	}

	private IIndependenceRelation<IPredicate, L> constructSemanticIndependence(final CfgSmtToolkit csToolkit) {
		return IndependenceBuilder.<L> semantic(mServices, constructIndependenceScript(),
				csToolkit.getManagedScript().getScript(), mConditionalPor, mSymmetricPor).build();
	}

	private IIndependenceRelation<IPredicate, L> constructConditionalIndependence(
			final IIndependenceRelation<IPredicate, L> semanticIndependence,
			final IIndependenceCache<IPredicate, L> independenceCache) {
		// Note: Soundness of the SemanticConditionEliminator depends on the fact that all inconsistent predicates are
		// syntactically equal to "false". Here, this is achieved by usage of DistributingIndependenceRelation: The only
		// predicates we use as conditions are the original interpolants (i.e., not conjunctions of them), where we
		// assume this constraint holds.
		return IndependenceBuilder.fromPredicateActionIndependence(semanticIndependence).cached(independenceCache)
				.withConditionElimination(PartialOrderCegarLoop::isFalseState).build();
	}

	private IIndependenceRelation<IPredicate, L> constructUnconditionalIndependence(
			final IIndependenceRelation<IPredicate, L> semanticIndependence,
			final IIndependenceCache<IPredicate, L> independenceCache) {
		return IndependenceBuilder.fromActionIndependence(semanticIndependence).ensureUnconditional()
				.withSyntacticCheck().cached(independenceCache).build();
	}

	private IIndependenceRelation<IPredicate, L>
			constructIndependenceRelation(final IIndependenceRelation<IPredicate, L> unconditionalRelation) {
		final IIndependenceRelation<IPredicate, L> independence;
		if (mConditionalPor) {
			mConjunctIndependenceRelations.add(unconditionalRelation);
			independence = new DistributingIndependenceRelation<>(mConjunctIndependenceRelations, this::getConjuncts);
		} else {
			independence = unconditionalRelation;
		}
		return new ThreadSeparatingIndependenceRelation<>(independence);
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

		final boolean isErrorState;
		if (state instanceof ISLPredicate) {
			isErrorState = mErrorLocs.contains(((ISLPredicate) state).getProgramPoint());
		} else {
			isErrorState = Arrays.stream(((IMLPredicate) state).getProgramPoints()).anyMatch(mErrorLocs::contains);
		}
		return isErrorState && !isProvenState(state);
	}

	private static boolean isProvenState(final IPredicate state) {
		if (state instanceof MLPredicateWithConjuncts) {
			// TODO possibly optimize and store this directly in the predicate?
			return ((MLPredicateWithConjuncts) state).getConjuncts().stream()
					.anyMatch(PartialOrderCegarLoop::isFalseState);
		}
		return isFalseState(state);
	}

	private static boolean isFalseState(final IPredicate state) {
		// We assume here that all inconsistent interpolant predicates are syntactically equal to "false".
		return SmtUtils.isFalseLiteral(state.getFormula());
	}

	private List<IPredicate> getConjuncts(final IPredicate conjunction) {
		if (conjunction == null) {
			return Collections.nCopies(mIteration + 1, null);
		}
		ImmutableList<IPredicate> tail;
		if (conjunction instanceof MLPredicateWithConjuncts) {
			tail = ((MLPredicateWithConjuncts) conjunction).getConjuncts();
		} else {
			tail = ImmutableList.empty();
		}
		return new ImmutableList<>(null, tail);
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
			final IPredicate newState =
					mPredicateFactory.construct(id -> new MLPredicateWithConjuncts(id, (IMLPredicate) state1, state2));

			// Transfer dead state info
			if (mVisitor instanceof DeadEndOptimizingSearchVisitor<?, ?, ?>) {
				final var deadEndVisitor = (DeadEndOptimizingSearchVisitor<?, IPredicate, ?>) mVisitor;
				if (deadEndVisitor.isDeadEndState(state1)) {
					deadEndVisitor.addDeadEndState(newState);
				}
			}

			return newState;
		}
	}
}
