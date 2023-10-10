/*
 * Copyright (C) 2022-2023 Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 * Copyright (C) 2022-2023 Daniel Küchler (kuechlerdaniel33@gmail.com)
 * Copyright (C) 2022-2023 University of Freiburg
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

package de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.cegar;

import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.BuchiComplementFKV;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.BuchiComplementNCSB;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.NestedLassoRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.IStateDeterminizer;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.PowersetDeterminizer;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.PetriNetLassoRun;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.PetriNetNot1SafeException;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.PetriNetRun;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.operations.BuchiIntersect;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.operations.DifferencePairwiseOnDemand;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.operations.RemoveDeadBuchi;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.BuchiIsEmpty;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.BuchiCegarLoopBenchmarkGenerator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.BuchiInterpolantAutomatonConstructionStyle;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.RankVarConstructor;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.Minimization;

/**
 * Cegar loop that uses Büchi-Petri-Nets
 *
 * @author Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 * @author Daniel Küchler (kuechlerdaniel33@gmail.com)
 *
 * @param <L>
 */
public class BuchiPetriNetCegarLoop<L extends IIcfgTransition<?>>
		extends AbstractBuchiCegarLoop<L, IPetriNet<L, IPredicate>> {
	private final Marking2MLPredicate mMarking2MLPredicate;

	public BuchiPetriNetCegarLoop(final IIcfg<?> icfg, final RankVarConstructor rankVarConstructor,
			final PredicateFactory predicateFactory, final TAPreferences taPrefs,
			final IUltimateServiceProvider services, final Class<L> transitionClazz,
			final IPetriNet<L, IPredicate> initialAbstraction,
			final BuchiCegarLoopBenchmarkGenerator benchmarkGenerator) {
		super(icfg, rankVarConstructor, predicateFactory, taPrefs, services, transitionClazz, initialAbstraction,
				benchmarkGenerator);
		mMarking2MLPredicate = new Marking2MLPredicate(predicateFactory);
	}

	@Override
	protected boolean isAbstractionEmpty(final IPetriNet<L, IPredicate> abstraction) throws AutomataLibraryException {
		final var isempty = new BuchiIsEmpty<>(new AutomataLibraryServices(mServices), abstraction, mPref.eventOrder(),
				mPref.cutOffRequiresSameTransition(), true);
		final PetriNetLassoRun<L, IPredicate> run = isempty.getRun();
		if (run == null) {
			return true;
		}
		mCounterexample =
				new NestedLassoRun<>(constructNestedLassoRun(run.getStem()), constructNestedLassoRun(run.getLoop()));
		return false;
	}

	private NestedRun<L, IPredicate> constructNestedLassoRun(final PetriNetRun<L, IPredicate> run) {
		return new NestedRun<>(NestedWord.nestedWord(run.getWord()), run.getStateSequence().stream()
				.map(mMarking2MLPredicate::markingToPredicate).collect(Collectors.toList()));
	}

	@Override
	protected IPetriNet<L, IPredicate> refineFinite(final IPetriNet<L, IPredicate> abstraction,
			final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> interpolantAutomaton)
			throws AutomataLibraryException {
		try {
			return new DifferencePairwiseOnDemand<>(new AutomataLibraryServices(mServices), abstraction,
					interpolantAutomaton).getResult();
		} catch (AutomataOperationCanceledException | PetriNetNot1SafeException e) {
			throw new AutomataLibraryException(getClass(), e.toString());
		}
	}

	@Override
	protected IPetriNet<L, IPredicate> refineBuchi(final IPetriNet<L, IPredicate> abstraction,
			final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> interpolantAutomaton,
			final BuchiInterpolantAutomatonConstructionStyle constructionStyle) throws AutomataLibraryException {
		final INestedWordAutomaton<L, IPredicate> complNwa;
		if (constructionStyle.isAlwaysSemiDeterministic()) {
			complNwa = new BuchiComplementNCSB<>(new AutomataLibraryServices(mServices), mDefaultStateFactory,
					interpolantAutomaton, true).getResult();
		} else {
			final IStateDeterminizer<L, IPredicate> stateDeterminizer =
					new PowersetDeterminizer<>(interpolantAutomaton, mUseDoubleDeckers, mDefaultStateFactory);
			final BuchiComplementFKV<L, IPredicate> fkvComplNwa =
					new BuchiComplementFKV<>(new AutomataLibraryServices(mServices), mDefaultStateFactory,
							interpolantAutomaton, stateDeterminizer);
			mBenchmarkGenerator.reportHighestRank(fkvComplNwa.getHighestRank());
			complNwa = fkvComplNwa.getResult();
		}
		final BuchiIntersect<L, IPredicate> intersection = new BuchiIntersect<>(new AutomataLibraryServices(mServices),
				mDefaultStateFactory, abstraction, complNwa);
		return intersection.getResult();
	}

	@Override
	protected IPetriNet<L, IPredicate> reduceAbstractionSize(final IPetriNet<L, IPredicate> abstraction,
			final Minimization automataMinimization) throws AutomataOperationCanceledException {
		try {
			return new RemoveDeadBuchi<>(new AutomataLibraryServices(mServices), abstraction, null).getResult();
		} catch (AutomataOperationCanceledException | PetriNetNot1SafeException e) {
			mLogger.warn(
					"Unhandled " + e + "occured during abstraction size reduction. Continuing with non-reduced net");
			return abstraction;
		}
	}
}
