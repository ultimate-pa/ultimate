/*
 * Copyright (C) 2022 Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 * Copyright (C) 2022 University of Freiburg
 *
 * This file is part of the ULTIMATE BuchiAutomizer plug-in.
 *
 * The ULTIMATE BuchiAutomizer plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE BuchiAutomizer plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE BuchiAutomizer plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE BuchiAutomizer plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE BuchiAutomizer plug-in grant you additional permission
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.cegar;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.BuchiCegarLoopBenchmarkGenerator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.BuchiInterpolantAutomatonBuilder;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.RankVarConstructor;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.Minimization;

/**
 * @author Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 */
public class BuchiPetriNetCegarLoop<L extends IIcfgTransition<?>>
		extends AbstractBuchiCegarLoop<L, IPetriNet<L, IPredicate>> {

	private final BuchiInterpolantAutomatonBuilder<L> mInterpolantAutomatonBuilder;

	public BuchiPetriNetCegarLoop(final IIcfg<?> icfg, final RankVarConstructor rankVarConstructor,
			final PredicateFactory predicateFactory, final TAPreferences taPrefs,
			final IUltimateServiceProvider services, final Class<L> transitionClazz,
			final IPetriNet<L, IPredicate> initialAbstraction,
			final BuchiCegarLoopBenchmarkGenerator benchmarkGenerator) {
		super(icfg, rankVarConstructor, predicateFactory, taPrefs, services, transitionClazz, initialAbstraction,
				benchmarkGenerator);
		mInterpolantAutomatonBuilder = new BuchiInterpolantAutomatonBuilder<>(mServices, mCsToolkitWithRankVars,
				SIMPLIFICATION_TECHNIQUE, XNF_CONVERSION_TECHNIQUE, mPredicateFactory, mDefaultStateFactory);
	}

	@Override
	protected boolean isAbstractionEmpty(final IPetriNet<L, IPredicate> abstraction) throws AutomataLibraryException {
		// TODO: Insert actual emptiness check (when finished)
		return false;
	}

	// @Override
	// protected IPetriNet<L, IPredicate> refineBuchi(final IPetriNet<L, IPredicate> abstraction,
	// final BinaryStatePredicateManager bspm) throws AutomataOperationCanceledException {
	// final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> interpolantAutomaton =
	// constructInterpolantAutomaton(bspm, new VpAlphabet<>(abstraction.getAlphabet()));
	// // TODO: Insert actual difference (when finished)
	// return null;
	// }
	//
	// private INwaOutgoingLetterAndTransitionProvider<L, IPredicate>
	// constructInterpolantAutomaton(final BinaryStatePredicateManager bspm, final VpAlphabet<L> alphabet) {
	// final PredicateUnifier pu = createPredicateUnifier(bspm);
	// final IPredicate[] stemInterpolants = getStemInterpolants(mCounterexample.getStem(), bspm, pu);
	// final IPredicate[] loopInterpolants = getLoopInterpolants(mCounterexample.getLoop(), bspm, pu);
	//
	// final NestedWordAutomaton<L, IPredicate> interpolAutomaton = mInterpolantAutomatonBuilder
	// .constructInterpolantAutomaton(bspm.getStemPrecondition(), mCounterexample, stemInterpolants,
	// bspm.getHondaPredicate(), loopInterpolants, alphabet, mDefaultStateFactory);
	// final IHoareTripleChecker ehtc = HoareTripleCheckerUtils.constructEfficientHoareTripleCheckerWithCaching(
	// mServices, HoareTripleChecks.INCREMENTAL, mCsToolkitWithRankVars, pu);
	// final BuchiHoareTripleChecker bhtc = new BuchiHoareTripleChecker(ehtc);
	// bhtc.putDecreaseEqualPair(bspm.getHondaPredicate(), bspm.getRankEqAndSi());
	// assert new InductivityCheck<>(mServices, interpolAutomaton, false, true, bhtc).getResult();
	// // TOOD: We should read this from the settings!
	// final BuchiInterpolantAutomatonConstructionStyle constructionStyle =
	// new BuchiInterpolantAutomatonConstructionStyle(BuchiInterpolantAutomaton.DETERMINISTIC, true, false,
	// false, false, false);
	// return mInterpolantAutomatonBuilder.constructGeneralizedAutomaton(mCounterexample, constructionStyle, bspm,
	// mInterpolation, pu, stemInterpolants, loopInterpolants, interpolAutomaton, bhtc);
	// }

	@Override
	protected IPetriNet<L, IPredicate> refineFinite(final IPetriNet<L, IPredicate> abstraction,
			final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> interpolantAutomaton)
			throws AutomataOperationCanceledException {
		// TODO: Insert actual difference (when finished). Is there a special case for finite automata?
		return null;
	}

	@Override
	protected IPetriNet<L, IPredicate> refineBuchi(final IPetriNet<L, IPredicate> abstraction,
			final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> interpolantAutomaton)
			throws AutomataOperationCanceledException {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	protected IPetriNet<L, IPredicate> reduceAbstractionSize(final IPetriNet<L, IPredicate> abstraction,
			final Minimization automataMinimization) throws AutomataOperationCanceledException {
		// TODO Auto-generated method stub
		return abstraction;
	}

}
