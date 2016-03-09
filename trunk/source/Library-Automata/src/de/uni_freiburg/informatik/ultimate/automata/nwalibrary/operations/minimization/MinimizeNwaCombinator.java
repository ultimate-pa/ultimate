/*
 * Copyright (C) 2016 Christian Schilling <schillic@informatik.uni-freiburg.de>
 * Copyright (C) 2009-2015 University of Freiburg
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
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonSimple;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;

/**
 * NWA minimization which can be used in a loop which just calls the next
 * minimization method according to a fixed pattern. The pattern is finite and
 * repeated.
 * 
 * @author Christian Schilling <schillic@informatik.uni-freiburg.de>
 */
public class MinimizeNwaCombinator<LETTER, STATE> extends
		AMinimizeNwa<LETTER, STATE> implements IOperation<LETTER, STATE> {
	/**
	 * Possible minimization algorithms.
	 */
	private enum EMinimizations {
		MinimizeSevpa,
		ShrinkNwa,
		None
	}
	
	// minimization algorithms executed from left to right
	private final EMinimizations[] mPattern;
	// current state in the pattern
	private final int mCounter;
	// current minimization method
	private final Object mCurrent;
	
	/**
	 * @param services services
	 * @param stateFactory state factory
	 * @param operand input automaton
	 * @throws AutomataLibraryException thrown by minimization methods
	 */
	public MinimizeNwaCombinator(final AutomataLibraryServices services,
			final StateFactory<STATE> stateFactory,
			final INestedWordAutomaton<LETTER, STATE> operand)
					throws AutomataLibraryException {
		this(services, stateFactory, operand, null, 0);
	}
	
	/**
	 * @param services services
	 * @param stateFactory state factory
	 * @param operand input automaton
	 * @param partition pre-defined partition of states
	 * @throws AutomataLibraryException thrown by minimization methods
	 */
	public MinimizeNwaCombinator(final AutomataLibraryServices services,
			final StateFactory<STATE> stateFactory,
			final INestedWordAutomaton<LETTER, STATE> operand,
			final Collection<Set<STATE>> partition,
			final int iteration)
					throws AutomataLibraryException {
		this(services, stateFactory, operand, partition, new EMinimizations[] {
				EMinimizations.None, EMinimizations.MinimizeSevpa,
				EMinimizations.None, EMinimizations.MinimizeSevpa,
				EMinimizations.None, EMinimizations.ShrinkNwa }, iteration);
	}
	
	/**
	 * /**
	 * @param services services
	 * @param stateFactory state factory
	 * @param operand input automaton
	 * @param partition pre-defined partition of states
	 * @param pattern minimization methods pattern
	 * @param iteration index in the pattern
	 * @throws AutomataLibraryException thrown by minimization methods
	 */
	public MinimizeNwaCombinator(final AutomataLibraryServices services,
			final StateFactory<STATE> stateFactory,
			final INestedWordAutomaton<LETTER, STATE> operand,
			final Collection<Set<STATE>> partition,
			final EMinimizations[] pattern, final int iteration)
					throws AutomataLibraryException {
		super(services, stateFactory, "MinimizeNwaCombinator", operand);
		mPattern = pattern;
		mCounter = iteration % mPattern.length;
		switch (mPattern[mCounter]) {
			case MinimizeSevpa:
				mCurrent = new MinimizeSevpa<LETTER, STATE>(services, operand,
						partition, stateFactory);
				break;
				
			case ShrinkNwa:
				mCurrent = new ShrinkNwa<LETTER, STATE>(services, stateFactory,
						operand, partition, true, false, false, 200, false, 0,
						false, false);
				break;
				
			case None:
				mCurrent = operand;
				break;
				
			default:
				throw new IllegalArgumentException("Undefined enum state.");
		}
	}
	
	@SuppressWarnings("unchecked")
	@Override
	public INestedWordAutomatonSimple<LETTER, STATE> getResult() {
		switch (mPattern[mCounter]) {
			case MinimizeSevpa:
				return ((MinimizeSevpa<LETTER, STATE>) mCurrent).getResult();
				
			case ShrinkNwa:
				return ((ShrinkNwa<LETTER, STATE>) mCurrent).getResult();
				
			case None:
				return (INestedWordAutomatonSimple<LETTER, STATE>) mCurrent;
				
			default:
				throw new IllegalArgumentException("Undefined enum state.");
		}
	}
	
	@SuppressWarnings("unchecked")
	public Map<STATE, STATE> getOldState2newState() {
		switch (mPattern[mCounter]) {
			case MinimizeSevpa:
				return ((MinimizeSevpa<LETTER, STATE>) mCurrent)
						.getOldState2newState();
						
			case ShrinkNwa:
				return ((ShrinkNwa<LETTER, STATE>) mCurrent)
						.getOldState2newState();
						
			case None:
				throw new IllegalArgumentException(
						"Do not ask for Hoare annotation if no minimization was used.");
						
			default:
				throw new IllegalArgumentException("Undefined enum state.");
		}
	}
	
	/**
	 * @return true iff backing minimization method supports Hoare annotation
	 */
	public boolean supportHoareAnnotation() {
		switch (mPattern[mCounter]) {
			case MinimizeSevpa:
			case ShrinkNwa:
				return true;
				
			case None:
				return false;
				
			default:
				throw new IllegalArgumentException("Undefined enum state.");
		}
	}
}