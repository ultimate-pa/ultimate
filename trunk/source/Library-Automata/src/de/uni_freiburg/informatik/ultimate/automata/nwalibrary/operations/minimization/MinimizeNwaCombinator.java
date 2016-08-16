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
package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.minimization;

import java.util.Collection;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.IDoubleDeckerAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;

/**
 * NWA minimization which can be used in a loop which just calls the next
 * minimization method according to a fixed pattern. The pattern is finite and
 * repeated.
 * 
 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
 * @param <LETTER> letter type
 * @param <STATE> state type
 */
public class MinimizeNwaCombinator<LETTER, STATE>
		extends AMinimizeNwaDD<LETTER, STATE>
		implements IOperation<LETTER, STATE> {
	/**
	 * Possible minimization algorithms.
	 */
	private enum EMinimizations {
		MINIMIZE_SEVPA,
		SHRINK_NWA,
		NONE
	}
	
	// minimization algorithms executed from left to right
	private final EMinimizations[] mPattern;
	// current state in the pattern
	private final int mCounter;
	// current minimization method
	private final Object mCurrent;
	
	/**
	 * AutomataScript constructor
	 * 
	 * @param services services
	 * @param stateFactory state factory
	 * @param operand input automaton
	 * @throws AutomataLibraryException thrown by minimization methods
	 */
	public MinimizeNwaCombinator(final AutomataLibraryServices services,
			final StateFactory<STATE> stateFactory,
			final IDoubleDeckerAutomaton<LETTER, STATE> operand)
					throws AutomataLibraryException {
		this(services, stateFactory, operand, null, false, 0);
	}
	
	/**
	 * constructor with default pattern
	 * 
	 * @param services services
	 * @param stateFactory state factory
	 * @param operand input automaton
	 * @param partition pre-defined partition of states
	 * @param addMapOldState2newState add map old state 2 new state?
	 * @param iteration index in the pattern
	 * @throws AutomataLibraryException thrown by minimization methods
	 */
	public MinimizeNwaCombinator(final AutomataLibraryServices services,
			final StateFactory<STATE> stateFactory,
			final IDoubleDeckerAutomaton<LETTER, STATE> operand,
			final Collection<Set<STATE>> partition,
			final boolean addMapOldState2newState,
			final int iteration)
					throws AutomataLibraryException {
		this(services, stateFactory, operand, partition, addMapOldState2newState,
				new EMinimizations[] {
					EMinimizations.NONE, EMinimizations.MINIMIZE_SEVPA,
					EMinimizations.NONE, EMinimizations.MINIMIZE_SEVPA,
					EMinimizations.NONE, EMinimizations.SHRINK_NWA }, iteration);
	}
	
	/**
	 * constructor with user-defined pattern
	 * 
	 * @param services services
	 * @param stateFactory state factory
	 * @param operand input automaton
	 * @param partition pre-defined partition of states
	 * @param addMapOldState2newState add map old state 2 new state?
	 * @param pattern minimization methods pattern
	 * @param iteration index in the pattern
	 * @throws AutomataLibraryException thrown by minimization methods
	 */
	public MinimizeNwaCombinator(final AutomataLibraryServices services,
			final StateFactory<STATE> stateFactory,
			final IDoubleDeckerAutomaton<LETTER, STATE> operand,
			final Collection<Set<STATE>> partition,
			final boolean addMapOldState2newState,
			final EMinimizations[] pattern, final int iteration)
					throws AutomataLibraryException {
		super(services, stateFactory, "MinimizeNwaCombinator", operand);
		mPattern = pattern;
		mCounter = iteration % mPattern.length;
		switch (mPattern[mCounter]) {
			case MINIMIZE_SEVPA:
				mCurrent = new MinimizeSevpa<LETTER, STATE>(services, operand,
						partition, stateFactory, addMapOldState2newState);
				break;
				
			case SHRINK_NWA:
				mCurrent = new ShrinkNwa<LETTER, STATE>(services, stateFactory,
						operand, partition, addMapOldState2newState, false,
						false, 200, false, 0, false, false);
				break;
				
			case NONE:
				mCurrent = operand;
				break;
				
			default:
				throw new IllegalArgumentException("Undefined enum state.");
		}
	}
	
	@SuppressWarnings("unchecked")
	@Override
	public IDoubleDeckerAutomaton<LETTER, STATE> getResult() {
		switch (mPattern[mCounter]) {
			case MINIMIZE_SEVPA:
				return ((MinimizeSevpa<LETTER, STATE>) mCurrent).getResult();
				
			case SHRINK_NWA:
				return ((ShrinkNwa<LETTER, STATE>) mCurrent).getResult();
				
			case NONE:
				return (IDoubleDeckerAutomaton<LETTER, STATE>) mCurrent;
				
			default:
				throw new IllegalArgumentException("Undefined enum state.");
		}
	}
	
	@SuppressWarnings("unchecked")
	@Override
	public Map<STATE, STATE> getOldState2newState() {
		switch (mPattern[mCounter]) {
			case MINIMIZE_SEVPA:
				return ((MinimizeSevpa<LETTER, STATE>) mCurrent)
						.getOldState2newState();
						
			case SHRINK_NWA:
				return ((ShrinkNwa<LETTER, STATE>) mCurrent)
						.getOldState2newState();
						
			case NONE:
				throw new IllegalArgumentException(
						"Do not ask for Hoare annotation if no minimization was used.");
						
			default:
				throw new IllegalArgumentException("Undefined enum state.");
		}
	}
}
