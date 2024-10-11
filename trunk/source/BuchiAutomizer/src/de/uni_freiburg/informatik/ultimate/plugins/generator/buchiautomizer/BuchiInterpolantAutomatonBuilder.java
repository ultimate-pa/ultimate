/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2013-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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

package de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer;

import java.util.Arrays;
import java.util.Collections;
import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.VpAlphabet;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.NestedLassoRun;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IEmptyStackStateFactory;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.RunningTaskInfo;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.ToolchainCanceledException;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateUnifier;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.singletracecheck.InterpolationTechnique;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.BinaryStatePredicateManager.BspmResult;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interpolantautomata.transitionappender.NondeterministicInterpolantAutomaton;

/**
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * @author Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 */
public class BuchiInterpolantAutomatonBuilder<LETTER extends IIcfgTransition<?>> {
	private final IUltimateServiceProvider mServices;
	private final CfgSmtToolkit mCsToolkit;
	private final SimplificationTechnique mSimplificationTechnique;
	private final PredicateFactory mPredicateFactory;
	private final InterpolationTechnique mInterpolation;

	public BuchiInterpolantAutomatonBuilder(final IUltimateServiceProvider services, final CfgSmtToolkit csToolkit,
			final SimplificationTechnique simplificationTechnique, final PredicateFactory predicateFactory,
			final InterpolationTechnique interpolation) {
		mServices = services;
		mCsToolkit = csToolkit;
		mSimplificationTechnique = simplificationTechnique;
		mPredicateFactory = predicateFactory;
		mInterpolation = interpolation;
	}

	public NestedWordAutomaton<LETTER, IPredicate> constructInterpolantAutomaton(final IPredicate precondition,
			final NestedLassoRun<LETTER, ?> counterexample, final IPredicate[] stemInterpolants, final IPredicate honda,
			final IPredicate[] loopInterpolants, final VpAlphabet<LETTER> vpAlphabet,
			final IEmptyStackStateFactory<IPredicate> emptyStateFactory) {
		final NestedWord<LETTER> stem = counterexample.getStem().getWord();
		final NestedWord<LETTER> loop = counterexample.getLoop().getWord();
		final NestedWordAutomaton<LETTER, IPredicate> result =
				new NestedWordAutomaton<>(new AutomataLibraryServices(mServices), vpAlphabet, emptyStateFactory);
		if (stem.length() == 0) {
			result.addState(true, true, honda);
		} else {
			result.addState(true, false, precondition);
			for (int i = 0; i < stemInterpolants.length; i++) {
				addState(stemInterpolants[i], result);
				addTransition(i, precondition, stemInterpolants, honda, stem, result);
			}
			result.addState(false, true, honda);
			addTransition(stemInterpolants.length, precondition, stemInterpolants, honda, stem, result);
		}
		for (int i = 0; i < loopInterpolants.length; i++) {
			addState(loopInterpolants[i], result);
			addTransition(i, honda, loopInterpolants, honda, loop, result);
		}
		addTransition(loopInterpolants.length, honda, loopInterpolants, honda, loop, result);
		return result;
	}

	private static void addState(final IPredicate pred, final NestedWordAutomaton<?, IPredicate> nwa) {
		if (!nwa.getStates().contains(pred)) {
			nwa.addState(false, false, pred);
		}
	}

	private static <LETTER extends IIcfgTransition<?>> void addTransition(final int pos, final IPredicate pre,
			final IPredicate[] predicates, final IPredicate post, final NestedWord<LETTER> nw,
			final NestedWordAutomaton<LETTER, IPredicate> nwa) {
		final IPredicate pred = getPredicateAtPosition(pos - 1, pre, predicates, post);
		final IPredicate succ = getPredicateAtPosition(pos, pre, predicates, post);
		final LETTER cb = nw.getSymbol(pos);
		if (nw.isInternalPosition(pos)) {
			nwa.addInternalTransition(pred, cb, succ);
		} else if (nw.isCallPosition(pos)) {
			nwa.addCallTransition(pred, cb, succ);
		} else if (nw.isReturnPosition(pos)) {
			assert !nw.isPendingReturn(pos);
			final int k = nw.getCallPosition(pos);
			final IPredicate hier = getPredicateAtPosition(k - 1, pre, predicates, post);
			nwa.addReturnTransition(pred, hier, cb, succ);
		}
	}

	private static IPredicate getPredicateAtPosition(final int pos, final IPredicate before,
			final IPredicate[] predicates, final IPredicate after) {
		assert pos >= -1;
		assert pos <= predicates.length;
		if (pos < 0) {
			return before;
		}
		if (pos >= predicates.length) {
			return after;
		}
		return predicates[pos];
	}

	public INwaOutgoingLetterAndTransitionProvider<LETTER, IPredicate> constructGeneralizedAutomaton(
			final NestedLassoRun<LETTER, IPredicate> counterexample,
			final BuchiInterpolantAutomatonConstructionStyle biaConstructionStyle, final BspmResult bspmResult,
			final PredicateUnifier pu, final IPredicate[] stemInterpolants, final IPredicate[] loopInterpolants,
			final NestedWordAutomaton<LETTER, IPredicate> interpolAutomaton, final BuchiHoareTripleChecker bhtc) {
		switch (biaConstructionStyle.getInterpolantAutomaton()) {
		case LASSO_AUTOMATON:
			return interpolAutomaton;
		case EAGER_NONDETERMINISM:
			if (!interpolAutomaton.getStates().contains(pu.getTruePredicate())) {
				interpolAutomaton.addState(false, false, pu.getTruePredicate());
			}
			if (!interpolAutomaton.getStates().contains(pu.getFalsePredicate())) {
				interpolAutomaton.addState(false, true, pu.getFalsePredicate());
			}
			return new NondeterministicInterpolantAutomaton<>(mServices, mCsToolkit, bhtc, interpolAutomaton, pu, false,
					true);
		case SCROOGE_NONDETERMINISM:
		case DETERMINISTIC:
			Set<IPredicate> stemInterpolantsForRefinement;
			if (BuchiAutomizerUtils.isEmptyStem(counterexample.getStem())) {
				stemInterpolantsForRefinement = Collections.emptySet();
			} else if (biaConstructionStyle.cannibalizeLoop()) {
				stemInterpolantsForRefinement = pu.cannibalizeAll(false, Arrays.asList(stemInterpolants));
			} else {
				stemInterpolantsForRefinement = new HashSet<>(Arrays.asList(stemInterpolants));
			}
			Set<IPredicate> loopInterpolantsForRefinement;
			if (biaConstructionStyle.cannibalizeLoop()) {
				try {
					loopInterpolantsForRefinement = pu.cannibalizeAll(false, Arrays.asList(loopInterpolants));
					loopInterpolantsForRefinement
							.addAll(pu.cannibalize(false, bspmResult.getRankEqAndSi().getFormula()));

					final LoopCannibalizer<LETTER> lc =
							new LoopCannibalizer<>(counterexample, loopInterpolantsForRefinement,
									bspmResult.getRankEqAndSi(), bspmResult.getHondaPredicate(), pu, mCsToolkit,
									mInterpolation, mServices, mSimplificationTechnique);
					loopInterpolantsForRefinement = lc.getResult();
				} catch (final ToolchainCanceledException tce) {
					final String taskDescription = "loop cannibalization";
					tce.addRunningTaskInfo(new RunningTaskInfo(getClass(), taskDescription));
					throw tce;
				}
			} else {
				loopInterpolantsForRefinement = new HashSet<>(Arrays.asList(loopInterpolants));
				loopInterpolantsForRefinement.add(bspmResult.getRankEqAndSi());
			}

			return new BuchiInterpolantAutomatonBouncer<>(mCsToolkit, mPredicateFactory, bspmResult, bhtc,
					counterexample, stemInterpolantsForRefinement, loopInterpolantsForRefinement, biaConstructionStyle,
					pu, mServices, interpolAutomaton);
		default:
			throw new UnsupportedOperationException("unknown automaton");
		}
	}
}
