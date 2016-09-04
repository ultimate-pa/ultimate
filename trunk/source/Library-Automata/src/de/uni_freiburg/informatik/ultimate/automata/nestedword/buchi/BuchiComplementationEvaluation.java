/*
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
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomatonSimple;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.UnaryNwaOperation;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.MultiOptimizationLevelRankingGenerator.FkvOptimization;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.RemoveNonLiveStates;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.RemoveUnreachable;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.MinimizeSevpa;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.reachablestates.NestedWordAutomatonReachableStates;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;

/**
 * Auxiliary class for doing some benchmarks.
 * 
 * @author heizmann@informatik.uni-freiburg.de
 * @param <LETTER>
 *            letter type
 * @param <STATE>
 *            state type
 */
public class BuchiComplementationEvaluation<LETTER, STATE> extends UnaryNwaOperation<LETTER, STATE> {
	
	private final INestedWordAutomaton<LETTER, STATE> mOperand;
	private final String mResult;
	
	@Override
	public String operationName() {
		return "BuchiComplementationEvaluation";
	}
	
	@Override
	public String exitMessage() {
		return "Finished " + operationName() + " Operand " + mOperand.sizeInformation() + " Result " + mResult;
	}
	
	public BuchiComplementationEvaluation(final AutomataLibraryServices services,
			final IStateFactory<STATE> stateFactory,
			final INestedWordAutomatonSimple<LETTER, STATE> input) throws AutomataLibraryException {
		super(services);
		this.mOperand = new NestedWordAutomatonReachableStates<>(mServices, input);
		mLogger.info(startMessage());
		mResult = evaluate(stateFactory);
		mLogger.info(exitMessage());
	}
	
	private String evaluate(final IStateFactory<STATE> stateFactory) throws AutomataLibraryException {
		final LinkedHashMap<String, Integer> results = new LinkedHashMap<>();
		{
			final String name = "BuchiComplementBS";
			final NestedWordAutomatonReachableStates<LETTER, STATE> result =
					(new BuchiComplementNCSB<LETTER, STATE>(mServices, stateFactory, mOperand)).getResult();
			addToResultsWithSizeReduction(results, name, result);
		}
		for (final FkvOptimization fkvOptimization : FkvOptimization.values()) {
			{
				final String name = "FKV_" + fkvOptimization;
				final NestedWordAutomatonReachableStates<LETTER, STATE> result =
						(new BuchiComplementFKV<LETTER, STATE>(mServices, stateFactory, mOperand,
								fkvOptimization.toString(), Integer.MAX_VALUE)).getResult();
				addToResultsWithSizeReduction(results, name, result);
			}
//			{
//				String name = "FKV_" + fkvOptimization + "_MaxRank3";
//			NestedWordAutomatonReachableStates<LETTER, STATE> result = (new BuchiComplementFKV<LETTER, STATE>(mServices,
//					stateFactory, mOperand, fkvOptimization.toString(), 3)).getResult();
//				addToResultsWithSizeReduction(results, name, result);
//			}
		}
		return prettyPrint(results);
	}
	
	private String prettyPrint(final LinkedHashMap<String, Integer> results) {
		final StringBuilder sb = new StringBuilder();
		for (final Entry<String, Integer> entry : results.entrySet()) {
			sb.append(entry.getKey());
			sb.append(" ");
			sb.append(entry.getValue());
			sb.append(System.lineSeparator());
		}
		return sb.toString();
	}
	
	private void addToResultsWithSizeReduction(final LinkedHashMap<String, Integer> results,
			final String name,
			final NestedWordAutomatonReachableStates<LETTER, STATE> result) throws AutomataLibraryException {
		addToResults(results, name, result);
		final INestedWordAutomaton<LETTER, STATE> nl =
				(new RemoveNonLiveStates<LETTER, STATE>(mServices, result)).getResult();
		addToResults(results, name + "_nonLiveRemoved", nl);
		final INestedWordAutomaton<LETTER, STATE> bc = (new BuchiClosure<LETTER, STATE>(mServices, nl)).getResult();
		final NestedWordAutomatonReachableStates<LETTER, STATE> bcru =
				(new RemoveUnreachable<LETTER, STATE>(mServices, bc)).getResult();
		final INestedWordAutomaton<LETTER, STATE> minmized =
				new MinimizeSevpa<LETTER, STATE>(mServices, bcru).getResult();
		addToResults(results, name + "_MsSizeReduction", minmized);
	}
	
	private void addToResults(final LinkedHashMap<String, Integer> results,
			final String name,
			final INestedWordAutomaton<LETTER, STATE> result) {
		final int size = result.getStates().size();
		results.put(name, size);
	}
	
	@Override
	public boolean checkResult(final IStateFactory<STATE> stateFactory)
			throws AutomataLibraryException {
		return true;
	}
	
	@Override
	protected INestedWordAutomatonSimple<LETTER, STATE> getOperand() {
		return mOperand;
	}
	
	@Override
	public String getResult() {
		return mResult;
	}
	
}
