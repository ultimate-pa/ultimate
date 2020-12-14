/*
 * Copyright (C) 2020 Marcel Ebbinghaus
 * Copyright (C) 2020 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2020 University of Freiburg
 *
 * This file is part of the ULTIMATE Automata Library.
 *
 * The ULTIMATE Automata Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Automata Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Automata Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Automata Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Automata Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.concurrency;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.InformationStorage;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.TotalizeNwa;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.CachedIndependenceRelation;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.ConstantSleepSetOrder;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.IIndependenceRelation;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.ISleepSetOrder;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.SleepSetDelayReduction;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.SleepSetNewStateReduction;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.SleepSetVisitorSearch;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.UnionIndependenceRelation;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.tempNewState;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.tempVisitorSearch;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IIntersectionStateFactory;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.debugidentifiers.DebugIdentifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IMLPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.ISLPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.singletracecheck.InterpolationTechnique;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.BasicCegarLoop;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.independencerelation.SemanticIndependenceRelation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.independencerelation.SyntacticIndependenceRelation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.petrinetlbe.PetriNetLargeBlockEncoding.IPLBECompositionFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;

public class SleepSetCegar<L extends IIcfgTransition<?>> extends BasicCegarLoop<L> {

	SleepSetVisitorSearch<L, IPredicate> mVisitor;
	//tempVisitorSearch<L, IPredicate> mVisitor;
	SleepSetMode mSleepSetMode;
	ArrayList<NestedWordAutomaton<L, IPredicate>> mInterpolantAutomataList = new ArrayList<>();

	public SleepSetCegar(final DebugIdentifier name, final IIcfg rootNode, final CfgSmtToolkit csToolkit,
			final PredicateFactory predicateFactory, final TAPreferences taPrefs, final Collection errorLocs,
			final InterpolationTechnique interpolation, final boolean computeHoareAnnotation,
			final IUltimateServiceProvider services, final IPLBECompositionFactory compositionFactory,
			final Class transitionClazz) {
		super(name, rootNode, csToolkit, predicateFactory, taPrefs, errorLocs, interpolation, computeHoareAnnotation,
				services, compositionFactory, transitionClazz);
		mSleepSetMode = mPref.getSleepSetMode();
	}

	@Override
	protected boolean refineAbstraction() throws AutomataLibraryException {
		return true;
	}

	@Override
	protected boolean isAbstractionEmpty() throws AutomataOperationCanceledException {
		final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> abstraction =
				(INwaOutgoingLetterAndTransitionProvider<L, IPredicate>) mAbstraction;

		final IIndependenceRelation<IPredicate, L> indep =
				new CachedIndependenceRelation<>(new UnionIndependenceRelation<>(
						Arrays.asList(new SyntacticIndependenceRelation<>(), new SemanticIndependenceRelation<>(
								mServices, mCsToolkit.getManagedScript(), mIteration > 0, true))));
		final ISleepSetOrder<IPredicate, L> order =
				new ConstantSleepSetOrder<>(abstraction.getVpAlphabet().getInternalAlphabet());

		final IIntersectionStateFactory<IPredicate> factory = new InformationStorageFactory();

		INwaOutgoingLetterAndTransitionProvider<L, IPredicate> newAbstraction = abstraction;
		for (final NestedWordAutomaton<L, IPredicate> interpolantAutomaton : mInterpolantAutomataList) {
			try {
				final TotalizeNwa<L, IPredicate> totalInterpol =
						new TotalizeNwa<>(interpolantAutomaton, mStateFactoryForRefinement, true);
				assert !totalInterpol.nonDeterminismInInputDetected() : "interpolant automaton was nondeterministic";
				newAbstraction = new InformationStorage<>(newAbstraction, totalInterpol, factory, false);
			} catch (final AutomataLibraryException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
		}
		mVisitor = new SleepSetVisitorSearch<>(this::isGoalState);
		//mVisitor = new tempVisitorSearch<>(this::isGoalState);
		
		if (mSleepSetMode == SleepSetMode.DELAY_SET) {
			new SleepSetDelayReduction<>(newAbstraction, indep, order, mVisitor);
		} else if (mSleepSetMode == SleepSetMode.NEW_STATES) {
			new SleepSetNewStateReduction<>(newAbstraction, indep, order, mSleepSetStateFactory, mVisitor);
			//new tempNewState<>(newAbstraction, indep, order, mSleepSetStateFactory, mVisitor);
		}

		mCounterexample = mVisitor.constructRun();

		if (mCounterexample == null) {
			return true;
		}

		return false;
	}

	@Override
	protected void constructInterpolantAutomaton() throws AutomataOperationCanceledException {
		super.constructInterpolantAutomaton();
		mInterpolantAutomataList.add(mInterpolAutomaton);
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
		// TODO (Dominik 2020-12-09): Below is a hack. Replace by a better solution.
		final boolean isFalse = state.getFormula().toString().equals("false");
		return isErrorState && !isFalse;
	}

	private final class InformationStorageFactory implements IIntersectionStateFactory<IPredicate> {
		@Override
		public IPredicate createEmptyStackState() {
			return mStateFactoryForRefinement.createEmptyStackState();
		}

		@Override
		public IPredicate intersection(final IPredicate state1, final IPredicate state2) {
			final Term formula;
			if (mPredicateFactory.isDontCare(state1)) {
				formula = state2.getFormula();
			} else {
				formula = mPredicateFactory.and(state1, state2).getFormula();
			}

			final IcfgLocation[] locations = ((IMLPredicate) state1).getProgramPoints();
			return mPredicateFactory.newMLPredicate(locations, formula);
		}
	}
}
