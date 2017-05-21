/*
 * Copyright (C) 2009-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2009-2015 University of Freiburg
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
 * along with the ULTIMATE Automata Library.  If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Automata Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Automata Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi;

import java.util.LinkedHashMap;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.UnaryNwaOperation;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.MultiOptimizationLevelRankingGenerator.FkvOptimization;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.RemoveNonLiveStates;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.RemoveUnreachable;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.IMinimizationStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.MinimizeSevpa;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.reachablestates.NestedWordAutomatonReachableStates;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IBuchiComplementFkvStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IBuchiComplementNcsbStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IDeterminizeStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;

/**
 * Auxiliary class for doing some benchmarks.
 * 
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @param <LETTER>
 *            letter type
 * @param <STATE>
 *            state type
 */
public final class BuchiComplementationEvaluation<LETTER, STATE>
		extends UnaryNwaOperation<LETTER, STATE, IStateFactory<STATE>> {
	private final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> mOperand;
	private final String mResult;

	/**
	 * Constructor.
	 * 
	 * @param services
	 *            Ultimate services
	 * @param stateFactory
	 *            state factory
	 * @param nwa
	 *            input nested word automaton
	 * @throws AutomataOperationCanceledException
	 *             if operation was canceled
	 */
	public <SF extends IBuchiComplementNcsbStateFactory<STATE> & IBuchiComplementFkvStateFactory<STATE> & IDeterminizeStateFactory<STATE>> BuchiComplementationEvaluation(
			final AutomataLibraryServices services, final SF stateFactory,
			final INwaOutgoingTransitionProvider<LETTER, STATE> nwa) throws AutomataOperationCanceledException {
		super(services);
		// TODO Christian 2016-09-18: This conversion is not necessary for receiving the required type. Use operand?
		mOperand = new NestedWordAutomatonReachableStates<>(mServices, nwa);

		if (mLogger.isInfoEnabled()) {
			mLogger.info(startMessage());
		}
		mResult = evaluate(stateFactory);
		if (mLogger.isInfoEnabled()) {
			mLogger.info(exitMessage());
		}
	}

	@Override
	public String exitMessage() {
		return "Finished " + getOperationName() + ". Operand " + mOperand.sizeInformation() + ". Result " + mResult;
	}

	@Override
	public boolean checkResult(final IStateFactory<STATE> stateFactory) throws AutomataLibraryException {
		return true;
	}

	@Override
	public String getResult() {
		return mResult;
	}

	@Override
	protected INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> getOperand() {
		return mOperand;
	}

	private <SF extends IBuchiComplementNcsbStateFactory<STATE> & IBuchiComplementFkvStateFactory<STATE> & IDeterminizeStateFactory<STATE>>
			String evaluate(final SF stateFactory) throws AutomataOperationCanceledException {
		final LinkedHashMap<String, Integer> results = new LinkedHashMap<>();
		evaluateBs(stateFactory, results);
		for (final FkvOptimization fkvOptimization : FkvOptimization.values()) {
			evaluateFkv(stateFactory, results, fkvOptimization);
			/*
			{
				String name = "FKV_" + fkvOptimization + "_MaxRank3";
			NestedWordAutomatonReachableStates<LETTER, STATE> result = (new BuchiComplementFKV<LETTER, STATE>(mServices,
					stateFactory, mOperand, fkvOptimization.toString(), 3)).getResult();
				addToResultsWithSizeReduction(results, name, result);
			}
			*/
		}
		return prettyPrint(results);
	}

	private void evaluateBs(final IBuchiComplementNcsbStateFactory<STATE> stateFactory,
			final LinkedHashMap<String, Integer> results) throws AutomataOperationCanceledException {
		final String name = "BuchiComplementBS";
		final NestedWordAutomatonReachableStates<LETTER, STATE> result =
				(new BuchiComplementNCSB<>(mServices, stateFactory, mOperand)).getResult();
		addToResultsWithSizeReduction(results, name, result);
	}

	private <SF extends IDeterminizeStateFactory<STATE> & IBuchiComplementFkvStateFactory<STATE>> void evaluateFkv(
			final SF stateFactory, final LinkedHashMap<String, Integer> results, final FkvOptimization fkvOptimization)
			throws AutomataOperationCanceledException {
		final String name = "FKV_" + fkvOptimization;
		final NestedWordAutomatonReachableStates<LETTER, STATE> result = (new BuchiComplementFKV<>(mServices,
				stateFactory, mOperand, fkvOptimization.toString(), Integer.MAX_VALUE)).getResult();
		addToResultsWithSizeReduction(results, name, result);
	}

	private static String prettyPrint(final LinkedHashMap<String, Integer> results) {
		final StringBuilder builder = new StringBuilder();
		for (final Entry<String, Integer> entry : results.entrySet()) {
			// @formatter:off
			builder.append(entry.getKey())
					.append(" ")
					.append(entry.getValue())
					.append(System.lineSeparator());
			// @formatter:on
		}
		return builder.toString();
	}

	private void addToResultsWithSizeReduction(final LinkedHashMap<String, Integer> results, final String name,
			final NestedWordAutomatonReachableStates<LETTER, STATE> result) throws AutomataOperationCanceledException {
		addToResults(results, name, result);
		final INestedWordAutomaton<LETTER, STATE> nl = (new RemoveNonLiveStates<>(mServices, result)).getResult();
		addToResults(results, name + "_nonLiveRemoved", nl);
		final INestedWordAutomaton<LETTER, STATE> bc = (new BuchiClosure<>(mServices, nl)).getResult();
		final NestedWordAutomatonReachableStates<LETTER, STATE> bcru =
				(new RemoveUnreachable<>(mServices, bc)).getResult();
		// TODO Christian 2017-01-27 somehow need a state factory here
		final INestedWordAutomaton<LETTER, STATE> minmized =
				new MinimizeSevpa<>(mServices, (IMinimizationStateFactory<STATE>) bcru.getStateFactory(), bcru)
						.getResult();
		addToResults(results, name + "_MsSizeReduction", minmized);
	}

	private void addToResults(final LinkedHashMap<String, Integer> results, final String name,
			final INestedWordAutomaton<LETTER, STATE> result) {
		final int size = result.getStates().size();
		results.put(name, size);
	}
}
