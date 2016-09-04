/*
 * Copyright (C) 2016 Christian Schilling (schillic@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations;

import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomatonSimple;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.UnaryNwaOperation;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingReturnTransition;

/**
 * Given an NWA, this class analyzes the NWA to obtain various information.
 * A user should use the respective getters to obtain individual data.
 * 
 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
 * @param <LETTER>
 *            letter type
 * @param <STATE>
 *            state type
 */
public class Analyze<LETTER, STATE>
		extends UnaryNwaOperation<LETTER, STATE>
		implements IOperation<LETTER, STATE> {
	/**
	 * Type of symbol.
	 */
	public enum ESymbolType {
		INTERNAL,
		CALL,
		RETURN,
		TOTAL
	}
	
	private final INestedWordAutomaton<LETTER, STATE> mOperand;
	
	private boolean mNumberOfStatesComputed;
	private int mNumberOfStates;
	
	private boolean mNumberOfSymbolsComputed;
	private int mNumberOfInternalSymbols;
	private int mNumberOfCallSymbols;
	private int mNumberOfReturnSymbols;
	
	private boolean mNumberOfTransitionsComputed;
	private int mNumberOfInternalTransitions;
	private int mNumberOfCallTransitions;
	private int mNumberOfReturnTransitions;
	
	private boolean mTransitionDensityComputed;
	private double mInternalTransitionDensity;
	private double mCallTransitionDensity;
	private double mReturnTransitionDensity;
	
	private boolean mNumberOfNondeterministicStatesComputed;
	private int mNumberOfNondeterministicStates;
	
	/**
	 * Base constructor.
	 * 
	 * @param services
	 *            Ultimate services
	 * @param operand
	 *            input NWA
	 */
	public Analyze(final AutomataLibraryServices services,
			final INestedWordAutomaton<LETTER, STATE> operand) {
		this(services, operand, false);
	}
	
	/**
	 * Extended constructor.
	 * 
	 * @param services
	 *            Ultimate services
	 * @param operand
	 *            input NWA
	 * @param computeEverything
	 *            true: information is computed at construction time;
	 *            false: information is computed at access time
	 */
	public Analyze(final AutomataLibraryServices services,
			final INestedWordAutomaton<LETTER, STATE> operand,
			final boolean computeEverything) {
		super(services);
		mOperand = operand;
		
		// compute all available information
		if (computeEverything) {
			getNumberOfStates();
			getNumberOfSymbols(ESymbolType.TOTAL);
			getNumberOfTransitions(ESymbolType.TOTAL);
			getTransitionDensity(ESymbolType.TOTAL);
			getNumberOfNondeterministicStates();
		}
	}
	
	// --- getter methods ---
	
	/**
	 * @return Number of states.
	 */
	public int getNumberOfStates() {
		if (!mNumberOfStatesComputed) {
			computeNumberOfStates();
		}
		return mNumberOfStates;
	}
	
	/**
	 * @param type
	 *            symbol type
	 * @return number of symbols
	 */
	public int getNumberOfSymbols(final ESymbolType type) {
		if (!mNumberOfSymbolsComputed) {
			computeNumberOfSymbols();
		}
		final int result;
		switch (type) {
			case INTERNAL:
				result = mNumberOfInternalSymbols;
				break;
				
			case CALL:
				result = mNumberOfCallSymbols;
				break;
				
			case RETURN:
				result = mNumberOfReturnSymbols;
				break;
				
			case TOTAL:
				result = mNumberOfInternalSymbols + mNumberOfCallSymbols + mNumberOfReturnSymbols;
				break;
				
			default:
				throw new IllegalArgumentException("Invalid symbol type.");
		}
		return result;
	}
	
	/**
	 * @param type
	 *            symbol type
	 * @return number of transitions
	 */
	public int getNumberOfTransitions(final ESymbolType type) {
		if (!mNumberOfTransitionsComputed) {
			computeNumberOfTransitions();
		}
		final int result;
		switch (type) {
			case INTERNAL:
				result = mNumberOfInternalTransitions;
				break;
				
			case CALL:
				result = mNumberOfCallTransitions;
				break;
				
			case RETURN:
				result = mNumberOfReturnTransitions;
				break;
				
			case TOTAL:
				result = mNumberOfInternalTransitions + mNumberOfCallTransitions + mNumberOfReturnTransitions;
				break;
				
			default:
				throw new IllegalArgumentException("Invalid symbol type.");
		}
		return result;
	}
	
	/**
	 * The transition density is defined as the number of transitions
	 * <code>T</code> divided by the number of states <code>S</code> and the
	 * number of symbols <code>L</code>. <br>
	 * transition density = <code>T / (S * L)</code> <br>
	 * <p>
	 * In particular, for return transitions the number of symbols
	 * <code>L</code> is the number of return symbol multiplied by the number
	 * of states.
	 * 
	 * @param type
	 *            symbol type
	 * @return transition density
	 */
	public double getTransitionDensity(final ESymbolType type) {
		if (!mTransitionDensityComputed) {
			computeTransitionDensity();
		}
		final double result;
		switch (type) {
			case INTERNAL:
				result = mInternalTransitionDensity;
				break;
				
			case CALL:
				result = mCallTransitionDensity;
				break;
				
			case RETURN:
				result = mReturnTransitionDensity;
				break;
				
			case TOTAL:
				result = (mInternalTransitionDensity + mCallTransitionDensity + mReturnTransitionDensity) / 3;
				break;
				
			default:
				throw new IllegalArgumentException("Invalid symbol type.");
		}
		return result;
	}
	
	/**
	 * A state is nondeterministic if it contains at least two outgoing
	 * transitions with the same symbol. <br>
	 * <p>
	 * In particular, for return transitions the same return symbol and
	 * hierarchical predecessor state must occur twice.
	 * 
	 * @return number of nondeterministic states
	 */
	public int getNumberOfNondeterministicStates() {
		if (!mNumberOfNondeterministicStatesComputed) {
			computeDegreeOfNondeterminism();
		}
		return mNumberOfNondeterministicStates;
	}
	
	// --- interface methods ---
	
	@Override
	public String operationName() {
		return "NWA Analysis";
	}
	
	@Override
	public String startMessage() {
		return "Started automaton analysis";
	}
	
	@Override
	public String exitMessage() {
		return "Finished automaton analysis";
	}

	@Override
	protected INestedWordAutomatonSimple<LETTER, STATE> getOperand() {
		return mOperand;
	}
	
	@Override
	public Object getResult() {
		return "NWA analysis result";
	}
	
	// --- computation methods ---
	
	private void computeNumberOfStates() {
		mNumberOfStates = mOperand.size();
		
		mNumberOfStatesComputed = true;
	}
	
	private void computeNumberOfSymbols() {
		mNumberOfInternalSymbols = mOperand.getInternalAlphabet().size();
		mNumberOfCallSymbols = mOperand.getCallAlphabet().size();
		mNumberOfReturnSymbols = mOperand.getReturnAlphabet().size();
		
		mNumberOfSymbolsComputed = true;
	}
	
	private void computeNumberOfTransitions() {
		mNumberOfInternalTransitions = 0;
		mNumberOfCallTransitions = 0;
		mNumberOfReturnTransitions = 0;
		
		for (final STATE state : mOperand.getStates()) {
			final Iterator<OutgoingInternalTransition<LETTER, STATE>> itI =
					mOperand.internalSuccessors(state).iterator();
			while (itI.hasNext()) {
				itI.next();
				++mNumberOfInternalTransitions;
			}
			
			final Iterator<OutgoingCallTransition<LETTER, STATE>> itC =
					mOperand.callSuccessors(state).iterator();
			while (itC.hasNext()) {
				itC.next();
				++mNumberOfCallTransitions;
			}
			
			final Iterator<OutgoingReturnTransition<LETTER, STATE>> itR =
					mOperand.returnSuccessors(state).iterator();
			while (itR.hasNext()) {
				itR.next();
				++mNumberOfReturnTransitions;
			}
		}
		
		mNumberOfTransitionsComputed = true;
	}
	
	@SuppressWarnings("squid:S1244")
	private void computeTransitionDensity() {
		// make sure the numbers of states, symbols, and transitions exist
		getNumberOfStates();
		getNumberOfSymbols(ESymbolType.TOTAL);
		getNumberOfTransitions(ESymbolType.TOTAL);
		
		double denominator;
		
		denominator = (mNumberOfStates * mNumberOfInternalSymbols);
		mInternalTransitionDensity = (denominator == 0d
				? 0d
				: (mNumberOfInternalTransitions / denominator));
				
		denominator = (mNumberOfStates * mNumberOfCallSymbols);
		mCallTransitionDensity = (denominator == 0d
				? 0d
				: (mNumberOfCallTransitions / denominator));
				
		denominator =
				(mNumberOfStates * mNumberOfStates * mNumberOfReturnSymbols);
		mReturnTransitionDensity = (denominator == 0d
				? 0d
				: (mNumberOfReturnTransitions / denominator));
				
		mTransitionDensityComputed = true;
	}
	
	private void computeDegreeOfNondeterminism() {
		mNumberOfNondeterministicStates = 0;
		
		final Set<STATE> dummySet = Collections.emptySet();
		final Map<LETTER, Set<STATE>> symbolsVisited = new HashMap<>();
		outer: for (final STATE state : mOperand.getStates()) {
			symbolsVisited.clear();
			for (final OutgoingInternalTransition<LETTER, STATE> trans : mOperand.internalSuccessors(state)) {
				if (symbolsVisited.put(trans.getLetter(), dummySet) != null) {
					++mNumberOfNondeterministicStates;
					continue outer;
				}
			}
			
			symbolsVisited.clear();
			for (final OutgoingCallTransition<LETTER, STATE> trans : mOperand.callSuccessors(state)) {
				if (symbolsVisited.put(trans.getLetter(), dummySet) != null) {
					++mNumberOfNondeterministicStates;
					continue outer;
				}
			}
			
			/*
			 * for return transitions check for same symbol AND hierarchical
			 * predecessor
			 */
			symbolsVisited.clear();
			for (final OutgoingReturnTransition<LETTER, STATE> trans : mOperand.returnSuccessors(state)) {
				final LETTER letter = trans.getLetter();
				Set<STATE> set = symbolsVisited.get(letter);
				if (set == null) {
					set = new HashSet<STATE>();
					symbolsVisited.put(letter, set);
				}
				if (!set.add(trans.getHierPred())) {
					++mNumberOfNondeterministicStates;
					continue outer;
				}
			}
		}
		
		mNumberOfNondeterministicStatesComputed = true;
	}
}
