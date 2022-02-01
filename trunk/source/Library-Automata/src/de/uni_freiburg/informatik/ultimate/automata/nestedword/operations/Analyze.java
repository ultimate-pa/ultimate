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
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.UnaryNwaOperation;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;

/**
 * Given a nested word automaton, this class analyzes the automaton to obtain various information.
 * <p>
 * A user should use the respective getters to obtain individual data.
 * 
 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
 * @param <LETTER>
 *            letter type
 * @param <STATE>
 *            state type
 */
public class Analyze<LETTER, STATE> extends UnaryNwaOperation<LETTER, STATE, IStateFactory<STATE>> {
	private static final String INVALID_SYMBOL_TYPE = "Invalid symbol type.";

	private static final int THREE = 3;

	/**
	 * Type of symbol.
	 */
	public enum SymbolType {
		/**
		 * Internal symbol.
		 */
		INTERNAL,
		/**
		 * Call symbol.
		 */
		CALL,
		/**
		 * Return symbol.
		 */
		RETURN,
		/**
		 * Any type of symbol.
		 */
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
	public Analyze(final AutomataLibraryServices services, final INestedWordAutomaton<LETTER, STATE> operand) {
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
	 *            true: information is computed at construction time; false: information is computed at access time
	 */
	public Analyze(final AutomataLibraryServices services, final INestedWordAutomaton<LETTER, STATE> operand,
			final boolean computeEverything) {
		super(services);
		mOperand = operand;

		// compute all available information
		if (computeEverything) {
			if (mLogger.isInfoEnabled()) {
				mLogger.info(startMessage());
			}

			getNumberOfStates();
			getNumberOfSymbols(SymbolType.TOTAL);
			getNumberOfTransitions(SymbolType.TOTAL);
			getTransitionDensity(SymbolType.TOTAL);
			getNumberOfNondeterministicStates();

			if (mLogger.isInfoEnabled()) {
				mLogger.info(exitMessage());
			}
		}
	}

	// --- getter methods ---

	/**
	 * @return Number of states.
	 */
	public final int getNumberOfStates() {
		if (!mNumberOfStatesComputed) {
			computeNumberOfStates();
		}
		return mNumberOfStates;
	}

	/**
	 * @param type
	 *            The symbol type.
	 * @return number of symbols
	 */
	public final int getNumberOfSymbols(final SymbolType type) {
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
				throw new IllegalArgumentException(INVALID_SYMBOL_TYPE);
		}
		return result;
	}

	/**
	 * @param type
	 *            The symbol type.
	 * @return number of transitions
	 */
	public final int getNumberOfTransitions(final SymbolType type) {
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
				throw new IllegalArgumentException(INVALID_SYMBOL_TYPE);
		}
		return result;
	}

	/**
	 * The transition density is defined as the number of transitions <code>T</code> divided by the number of states
	 * <code>S</code> and the number of symbols <code>L</code>. <br>
	 * transition density = <code>T / (S * L)</code> <br>
	 * <p>
	 * In particular, for return transitions the number of symbols <code>L</code> is the number of return symbol
	 * multiplied by the number of states.
	 * 
	 * @param type
	 *            symbol type
	 * @return transition density
	 */
	public final double getTransitionDensity(final SymbolType type) {
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
				result = (mInternalTransitionDensity + mCallTransitionDensity + mReturnTransitionDensity) / THREE;
				break;

			default:
				throw new IllegalArgumentException(INVALID_SYMBOL_TYPE);
		}
		return result;
	}

	/**
	 * A state is nondeterministic if it contains at least two outgoing transitions with the same symbol. <br>
	 * <p>
	 * In particular, for return transitions the same return symbol and hierarchical predecessor state must occur twice.
	 * 
	 * @return number of nondeterministic states
	 */
	public final int getNumberOfNondeterministicStates() {
		if (!mNumberOfNondeterministicStatesComputed) {
			computeDegreeOfNondeterminism();
		}
		return mNumberOfNondeterministicStates;
	}

	// --- interface methods ---

	@Override
	public final String startMessage() {
		return "Started automaton analysis";
	}

	@Override
	public final String exitMessage() {
		return "Finished automaton analysis";
	}

	@Override
	protected INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> getOperand() {
		return mOperand;
	}

	@Override
	public Object getResult() {
		return "NWA analysis result";
	}

	// --- computation methods ---

	private final void computeNumberOfStates() {
		mNumberOfStates = mOperand.size();

		mNumberOfStatesComputed = true;
	}

	private final void computeNumberOfSymbols() {
		mNumberOfInternalSymbols = mOperand.getVpAlphabet().getInternalAlphabet().size();
		mNumberOfCallSymbols = mOperand.getVpAlphabet().getCallAlphabet().size();
		mNumberOfReturnSymbols = mOperand.getVpAlphabet().getReturnAlphabet().size();

		mNumberOfSymbolsComputed = true;
	}

	private final void computeNumberOfTransitions() {
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

			final Iterator<OutgoingCallTransition<LETTER, STATE>> itC = mOperand.callSuccessors(state).iterator();
			while (itC.hasNext()) {
				itC.next();
				++mNumberOfCallTransitions;
			}

			final Iterator<OutgoingReturnTransition<LETTER, STATE>> itR = mOperand.returnSuccessors(state).iterator();
			while (itR.hasNext()) {
				itR.next();
				++mNumberOfReturnTransitions;
			}
		}

		mNumberOfTransitionsComputed = true;
	}

	@SuppressWarnings({ "squid:S1244", "squid:S2184" })
	private void computeTransitionDensity() {
		// make sure the numbers of states, symbols, and transitions exist
		getNumberOfStates();
		getNumberOfSymbols(SymbolType.TOTAL);
		getNumberOfTransitions(SymbolType.TOTAL);

		double denominator;

		denominator = mNumberOfStates * mNumberOfInternalSymbols;
		mInternalTransitionDensity = denominator == 0D ? 0D : (mNumberOfInternalTransitions / denominator);

		denominator = mNumberOfStates * mNumberOfCallSymbols;
		mCallTransitionDensity = denominator == 0D ? 0D : (mNumberOfCallTransitions / denominator);

		denominator = mNumberOfStates * mNumberOfStates * mNumberOfReturnSymbols;
		mReturnTransitionDensity = denominator == 0D ? 0D : (mNumberOfReturnTransitions / denominator);

		mTransitionDensityComputed = true;
	}

	private final void computeDegreeOfNondeterminism() {
		mNumberOfNondeterministicStates = 0;

		final Set<STATE> dummySet = Collections.emptySet();
		for (final STATE state : mOperand.getStates()) {
			computeDegreeOfNondeterminismInternal(dummySet, state);

			computeDegreeOfNondeterminismCall(dummySet, state);

			computeDegreeOfNondeterminismReturn(state);
		}

		mNumberOfNondeterministicStatesComputed = true;
	}

	private void computeDegreeOfNondeterminismInternal(final Set<STATE> dummySet, final STATE state) {
		final Map<LETTER, Set<STATE>> symbolsVisited = new HashMap<>();
		for (final OutgoingInternalTransition<LETTER, STATE> trans : mOperand.internalSuccessors(state)) {
			if (symbolsVisited.put(trans.getLetter(), dummySet) != null) {
				++mNumberOfNondeterministicStates;
				return;
			}
		}
	}

	private void computeDegreeOfNondeterminismCall(final Set<STATE> dummySet, final STATE state) {
		final Map<LETTER, Set<STATE>> symbolsVisited = new HashMap<>();
		for (final OutgoingCallTransition<LETTER, STATE> trans : mOperand.callSuccessors(state)) {
			if (symbolsVisited.put(trans.getLetter(), dummySet) != null) {
				++mNumberOfNondeterministicStates;
				return;
			}
		}
	}

	private void computeDegreeOfNondeterminismReturn(final STATE state) {
		/*
		 * for return transitions check for same symbol AND hierarchical
		 * predecessor
		 */
		final Map<LETTER, Set<STATE>> symbolsVisited = new HashMap<>();
		for (final OutgoingReturnTransition<LETTER, STATE> trans : mOperand.returnSuccessors(state)) {
			final LETTER letter = trans.getLetter();
			Set<STATE> set = symbolsVisited.get(letter);
			if (set == null) {
				set = new HashSet<>();
				symbolsVisited.put(letter, set);
			}
			if (!set.add(trans.getHierPred())) {
				++mNumberOfNondeterministicStates;
				return;
			}
		}
	}
}
