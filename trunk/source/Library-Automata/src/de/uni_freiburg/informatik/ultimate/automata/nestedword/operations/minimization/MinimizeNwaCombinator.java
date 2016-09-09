/*
 * Copyright (C) 2016 Christian Schilling (schillic@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
 * 
 * This file is part of the ULTIMATE Automata Library.
 * 
 * The ULTIMATE Automata Library is free software: you can redistribute it
 * and/or modify it under the terms of the GNU Lesser General Public License as
 * published by the Free Software Foundation, either version 3 of the License,
 * or (at your option) any later version.
 * 
 * The ULTIMATE Automata Library is distributed in the hope that it will be
 * useful, but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU Lesser
 * General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Automata Library. If not, see
 * <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7: If you modify the
 * ULTIMATE Automata Library, or any covered work, by linking or combining it
 * with Eclipse RCP (or a modified version of Eclipse RCP), containing parts
 * covered by the terms of the Eclipse Public License, the licensors of the
 * ULTIMATE Automata Library grant you additional permission to convey the
 * resulting work.
 */
package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization;

import java.util.Arrays;
import java.util.Collection;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.IDoubleDeckerAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;

/**
 * NWA minimization which can be used in a loop which just calls the next
 * minimization method according to a fixed pattern. The pattern is finite and
 * repeated.
 * 
 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
 * @param <LETTER>
 *            letter type
 * @param <STATE>
 *            state type
 */
public class MinimizeNwaCombinator<LETTER, STATE> extends AbstractMinimizeNwaDd<LETTER, STATE> {
	private static final String UNDEFINED_ENUM_STATE_MESSAGE = "Undefined enum state.";
	
	/**
	 * Possible minimization methods.
	 */
	private enum MinimizationMethods {
		MINIMIZE_SEVPA,
		SHRINK_NWA,
		NONE
	}
	
	// minimization algorithms executed from left to right
	private final MinimizationMethods[] mPattern;
	// current state in the pattern
	private final int mCounter;
	// current minimization method
	private final Object mCurrent;
	
	/**
	 * AutomataScript constructor with default settings.
	 * <ul>
	 * <li>no initial partition</li>
	 * <li>no mapping 'old state -> new state'</li>
	 * <li>default pattern</li>
	 * </ul>
	 * <p>
	 * NOTE: It makes little sense to use this operation from the AutomataScript interface as only the first operation
	 * is executed.
	 * 
	 * @param services
	 *            services
	 * @param stateFactory
	 *            state factory
	 * @param operand
	 *            input automaton
	 * @throws AutomataOperationCanceledException
	 *             if operation was canceled
	 */
	public MinimizeNwaCombinator(final AutomataLibraryServices services,
			final IStateFactory<STATE> stateFactory,
			final IDoubleDeckerAutomaton<LETTER, STATE> operand)
			throws AutomataOperationCanceledException {
		this(services, stateFactory, operand, null, false, 0);
	}
	
	/**
	 * Constructor with default pattern.
	 * 
	 * @param services
	 *            services
	 * @param stateFactory
	 *            state factory
	 * @param operand
	 *            input automaton
	 * @param partition
	 *            pre-defined partition of states
	 * @param addMapOldState2newState
	 *            add map old state 2 new state?
	 * @param iteration
	 *            index in the pattern
	 * @throws AutomataOperationCanceledException
	 *             if operation was canceled
	 */
	public MinimizeNwaCombinator(final AutomataLibraryServices services,
			final IStateFactory<STATE> stateFactory,
			final IDoubleDeckerAutomaton<LETTER, STATE> operand,
			final Collection<Set<STATE>> partition,
			final boolean addMapOldState2newState,
			final int iteration)
			throws AutomataOperationCanceledException {
		this(services, stateFactory, operand, partition, addMapOldState2newState, getDefaultPattern(), iteration);
	}
	
	/**
	 * Constructor using only one minimization operation every {@code k}th iteration.
	 * 
	 * @param services
	 *            services
	 * @param stateFactory
	 *            state factory
	 * @param operand
	 *            input automaton
	 * @param partition
	 *            pre-defined partition of states
	 * @param addMapOldState2newState
	 *            add map old state 2 new state?
	 * @param indexForMinimization
	 *            iteration index at which minimization should be used
	 * @param iteration
	 *            index in the pattern
	 * @throws AutomataOperationCanceledException
	 *             if operation was canceled
	 */
	public MinimizeNwaCombinator(final AutomataLibraryServices services,
			final IStateFactory<STATE> stateFactory,
			final IDoubleDeckerAutomaton<LETTER, STATE> operand,
			final Collection<Set<STATE>> partition,
			final boolean addMapOldState2newState,
			final int indexForMinimization,
			final int iteration)
			throws AutomataOperationCanceledException {
		this(services, stateFactory, operand, partition, addMapOldState2newState,
				getEveryNthPattern(indexForMinimization), iteration);
	}
	
	/**
	 * Constructor with user-defined pattern.
	 * 
	 * @param services
	 *            services
	 * @param stateFactory
	 *            state factory
	 * @param operand
	 *            input automaton
	 * @param partition
	 *            pre-defined partition of states
	 * @param addMapOldState2newState
	 *            add map old state 2 new state?
	 * @param pattern
	 *            minimization methods pattern
	 * @param iteration
	 *            index in the pattern
	 * @throws AutomataOperationCanceledException
	 *             if operation was canceled
	 */
	public MinimizeNwaCombinator(final AutomataLibraryServices services,
			final IStateFactory<STATE> stateFactory,
			final IDoubleDeckerAutomaton<LETTER, STATE> operand,
			final Collection<Set<STATE>> partition,
			final boolean addMapOldState2newState,
			final MinimizationMethods[] pattern, final int iteration)
			throws AutomataOperationCanceledException {
		super(services, stateFactory, "MinimizeNwaCombinator", operand);
		mPattern = Arrays.copyOf(pattern, pattern.length);
		mCounter = iteration % mPattern.length;
		switch (mPattern[mCounter]) {
			case MINIMIZE_SEVPA:
				mCurrent = new MinimizeSevpa<LETTER, STATE>(services, operand,
						partition, stateFactory, addMapOldState2newState);
				break;
			
			case SHRINK_NWA:
				mCurrent = new ShrinkNwa<LETTER, STATE>(services, stateFactory,
						operand, partition, addMapOldState2newState, false,
						false, ShrinkNwa.SUGGESTED_RANDOM_SPLIT_SIZE, false, 0, false, false, true);
				break;
			
			case NONE:
				mLogger.info("No minimization is used.");
				mCurrent = operand;
				break;
			
			default:
				throw new IllegalArgumentException(UNDEFINED_ENUM_STATE_MESSAGE);
		}
	}
	
	/**
	 * Creates a pattern where minimization is only used in each {@code k}th iteration.
	 * 
	 * @param indexForMinimization
	 *            index at which the minimization should actually be used
	 * @return pattern
	 */
	private static MinimizationMethods[] getEveryNthPattern(final int indexForMinimization) {
		if (indexForMinimization <= 0) {
			throw new IllegalArgumentException("The minimization index must be strictly positive.");
		}
		
		final MinimizationMethods[] pattern = new MinimizationMethods[indexForMinimization];
		pattern[indexForMinimization - 1] = MinimizationMethods.MINIMIZE_SEVPA;
		for (int i = indexForMinimization - 2; i >= 0; --i) {
			pattern[i] = MinimizationMethods.NONE;
		}
		return pattern;
	}
	
	/**
	 * @return The default pattern.
	 */
	private static MinimizationMethods[] getDefaultPattern() {
		return new MinimizationMethods[] {
				MinimizationMethods.NONE, MinimizationMethods.MINIMIZE_SEVPA,
				MinimizationMethods.NONE, MinimizationMethods.MINIMIZE_SEVPA,
				MinimizationMethods.NONE, MinimizationMethods.SHRINK_NWA };
	}
	
	@SuppressWarnings("unchecked")
	@Override
	public IDoubleDeckerAutomaton<LETTER, STATE> getResult() {
		switch (mPattern[mCounter]) {
			case MINIMIZE_SEVPA:
				return (IDoubleDeckerAutomaton<LETTER, STATE>) ((MinimizeSevpa<LETTER, STATE>) mCurrent).getResult();
			
			case SHRINK_NWA:
				return ((ShrinkNwa<LETTER, STATE>) mCurrent).getResult();
			
			case NONE:
				return (IDoubleDeckerAutomaton<LETTER, STATE>) mCurrent;
			
			default:
				throw new IllegalArgumentException(UNDEFINED_ENUM_STATE_MESSAGE);
		}
	}

	@SuppressWarnings("unchecked")
	@Override
	public Map<STATE, STATE> getOldState2newState() {
		switch (mPattern[mCounter]) {
			case MINIMIZE_SEVPA:
				return ((MinimizeSevpa<LETTER, STATE>) mCurrent).getOldState2newState();
			
			case SHRINK_NWA:
				return ((ShrinkNwa<LETTER, STATE>) mCurrent).getOldState2newState();
			
			case NONE:
				throw new IllegalArgumentException(
						"Do not ask for Hoare annotation if no minimization was used.");
				
			default:
				throw new IllegalArgumentException(UNDEFINED_ENUM_STATE_MESSAGE);
		}
	}
	
	@SuppressWarnings("unchecked")
	@Override
	public boolean checkResult(final IStateFactory<STATE> stateFactory) throws AutomataLibraryException {
		switch (mPattern[mCounter]) {
			case MINIMIZE_SEVPA:
				return ((MinimizeSevpa<LETTER, STATE>) mCurrent).checkResult(stateFactory);
			
			case SHRINK_NWA:
				return ((ShrinkNwa<LETTER, STATE>) mCurrent).checkResult(stateFactory);
			
			case NONE:
				return true;
			
			default:
				throw new IllegalArgumentException(UNDEFINED_ENUM_STATE_MESSAGE);
		}
	}
}
