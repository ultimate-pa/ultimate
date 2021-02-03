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
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.InformationStorage;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.TotalizeNwa;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.CachedIndependenceRelation;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.CachedIndependenceRelation.IIndependenceCache;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.ConstantSleepSetOrder;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.DefaultIndependenceCache;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.IIndependenceRelation;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.ISleepSetOrder;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.SleepSetDelayReduction;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.SleepSetNewStateReduction;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.SleepSetVisitorSearch;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.UnionIndependenceRelation;
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
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.singletracecheck.InterpolationTechnique;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.BasicCegarLoop;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.independencerelation.SemanticIndependenceRelation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.independencerelation.SyntacticIndependenceRelation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interpolantautomata.transitionappender.AbstractInterpolantAutomaton;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.petrinetlbe.PetriNetLargeBlockEncoding.IPLBECompositionFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;

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
	private final SleepSetVisitorSearch<L, IPredicate> mVisitor;

	// Maps an IPredicate built through refinement rounds to the sequence of conjuncts it was built from.
	// This is used to distribute an independence query across conjuncts.
	private final Map<IPredicate, IPredicate[]> mPredicateConjuncts = new HashMap<>();

	private ISleepSetOrder<IPredicate, L> mSleepSetOrder;
	private final List<IIndependenceRelation<IPredicate, L>> mIndependenceRelations = new ArrayList<>();
	private final IIndependenceCache<IPredicate, L> mIndependenceCache;

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
		mVisitor = new SleepSetVisitorSearch<>(this::isGoalState, PartialOrderCegarLoop::isFalseState);

		// Note: Soundness of this normalizer depends on the fact that all inconsistent predicates are syntactically
		// equal to "false". Here, this is achieved by usage of the DistributingIndependenceRelation below: The only
		// predicates we use are the original interpolants (i.e., not conjunctions of them), where we assume this
		// condition holds.
		mIndependenceCache = new DefaultIndependenceCache<>(
				new SemanticIndependenceRelation.ConditionNormalizer<>(PartialOrderCegarLoop::isFalseState));
	}

	@Override
	protected void getInitialAbstraction() throws AutomataLibraryException {
		super.getInitialAbstraction();
		mSleepSetOrder =
				new ConstantSleepSetOrder<>(((INwaOutgoingLetterAndTransitionProvider<L, IPredicate>) mAbstraction)
						.getVpAlphabet().getInternalAlphabet());
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
		}

		// Automaton must be total and deterministic
		final TotalizeNwa<L, IPredicate> totalInterpol = new TotalizeNwa<>(ia, mStateFactoryForRefinement, true);
		assert !totalInterpol.nonDeterminismInInputDetected() : "interpolant automaton was nondeterministic";

		// Actual refinement step
		final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> oldAbstraction =
				(INwaOutgoingLetterAndTransitionProvider<L, IPredicate>) mAbstraction;
		mAbstraction = new InformationStorage<>(oldAbstraction, totalInterpol, mFactory, false);

		// TODO (Dominik 2020-12-17) Really implement this acceptance check (see BasicCegarLoop::refineAbstraction)
		return true;
	}

	@Override
	protected boolean isAbstractionEmpty() throws AutomataOperationCanceledException {
		final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> abstraction =
				(INwaOutgoingLetterAndTransitionProvider<L, IPredicate>) mAbstraction;

		final IIndependenceRelation<IPredicate, L> newIndependence;
		if (mIteration == 0) {
			newIndependence = new CachedIndependenceRelation<>(
					new UnionIndependenceRelation<>(Arrays.asList(new SyntacticIndependenceRelation<>(),
							new SemanticIndependenceRelation<>(mServices, mCsToolkit.getManagedScript(), false, true))),
					mIndependenceCache);
		} else {
			newIndependence = new CachedIndependenceRelation<>(
					new SemanticIndependenceRelation<>(mServices, mCsToolkit.getManagedScript(), true, true),
					mIndependenceCache);
		}
		mIndependenceRelations.add(newIndependence);
		final IIndependenceRelation<IPredicate, L> indep = new DistributingIndependenceRelation(mIndependenceRelations);

		switchToOnDemandConstructionMode();
		switch (mPartialOrderMode) {
		case SLEEP_DELAY_SET:
			new SleepSetDelayReduction<>(abstraction, indep, mSleepSetOrder, mVisitor);
			break;
		case SLEEP_NEW_STATES:
			new SleepSetNewStateReduction<>(abstraction, indep, mSleepSetOrder, mSleepSetStateFactory, mVisitor);
			break;
		default:
			throw new UnsupportedOperationException("Unsupported POR mode: " + mPartialOrderMode);
		}
		mCounterexample = mVisitor.constructRun();
		switchToReadonlyMode();

		return mCounterexample == null;
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
		// TODO (Dominik 2020-12-09): Below is a hack. Replace by a better solution.
		return state.getFormula().toString().equals("false");
	}

	private IPredicate[] getConjuncts(final IPredicate conjunction) {
		return mPredicateConjuncts.getOrDefault(conjunction, new IPredicate[] { conjunction });
	}

	private final class DistributingIndependenceRelation implements IIndependenceRelation<IPredicate, L> {
		private final List<IIndependenceRelation<IPredicate, L>> mRelations;
		private final boolean mSymmetric;
		private final boolean mConditional;

		public DistributingIndependenceRelation(final List<IIndependenceRelation<IPredicate, L>> relations) {
			mRelations = relations;
			mSymmetric = relations.stream().allMatch(IIndependenceRelation::isSymmetric);
			mConditional = relations.stream().anyMatch(IIndependenceRelation::isConditional);
		}

		@Override
		public boolean isSymmetric() {
			return mSymmetric;
		}

		@Override
		public boolean isConditional() {
			return mConditional;
		}

		@Override
		public boolean contains(final IPredicate state, final L a, final L b) {
			final IPredicate[] conjuncts = getConjuncts(state);
			assert conjuncts.length == mRelations.size();
			for (int i = 0; i < mRelations.size(); ++i) {
				if (mRelations.get(i).contains(conjuncts[i], a, b)) {
					return true;
				}
			}
			return false;
		}
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
			if (mVisitor.isDeadEndState(state1)) {
				mVisitor.addDeadEndState(newState);
			}

			return newState;
		}
	}
}
