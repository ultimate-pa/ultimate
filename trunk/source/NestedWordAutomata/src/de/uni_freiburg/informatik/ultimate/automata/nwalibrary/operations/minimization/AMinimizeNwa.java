/*
 * Copyright (C) 2009-2014 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.minimization;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.NestedWordAutomata;
import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.ResultChecker;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonSimple;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.IsDeterministic;

/**
 * This is the superclass of all minimization classes.
 * It provides a correctness check for all subclasses and an optional DFA check
 * for subclasses that only work for DFAs.
 * 
 * Since the classes of the <code>NwaLibrary.Operations</code> package must
 * automatically execute their operations from within the constructor call, the
 * correctness check cannot be inherited automatically. Hence all implementing
 * subclasses must explicitly call the respective method themselves.
 * 
 * @author Christian
 */
public abstract class AMinimizeNwa<LETTER, STATE>
		implements IOperation<LETTER, STATE> {
	/**
	 * The logger.
	 */
	protected static final Logger s_logger = 
			NestedWordAutomata.getLogger();
	
	/**
	 * The operation name.
	 */
	protected final String m_name;
	
	/**
	 * The input automaton.
	 */
	protected final INestedWordAutomaton<LETTER, STATE> m_operand;
	
	/**
	 * StateFactory for the construction of states of the resulting automaton.
	 */
	protected final StateFactory<STATE> m_StateFactory;

	/**
	 * This constructor should be called by all subclasses and only by them.
	 * 
	 * @param name operation name
	 * @param operand input automaton
	 */
	protected AMinimizeNwa(StateFactory<STATE> stateFactory, final String name,
			final INestedWordAutomaton<LETTER, STATE> operand) {
		m_name = name;
		m_operand = operand;
		m_StateFactory = stateFactory;
		s_logger.info(startMessage());
	}
	
	@Override
	public final String operationName() {
		return m_name;
	}
	
	@Override
	public final String startMessage() {
		return "Start " + operationName() + ". Operand has " +
			m_operand.sizeInformation();
	}
	
	@Override
	public final String exitMessage() {
		return "Finished " + operationName() + ". Reduced states from " +
				m_operand.size() + " to " + getResult().size() + ".";
	}
	
	@Override
	public abstract INestedWordAutomatonSimple<LETTER,STATE> getResult();
	
	@Override
	public final boolean checkResult(final StateFactory<STATE> stateFactory)
			throws AutomataLibraryException {
		s_logger.info("Start testing correctness of " + operationName());
		final String message;
		
		if (checkInclusion(m_operand, getResult(), stateFactory)) {
			if (checkInclusion(getResult(), m_operand, stateFactory)) {
				s_logger.info("Finished testing correctness of " +
						operationName());
				return true;
			}
			else {
				message = "The result recognizes less words than before.";
			}
		}
		else {
			message = "The result recognizes more words than before.";
		}
		
		ResultChecker.writeToFileIfPreferred(
				operationName() + " failed",
				message,
				m_operand);
		return false;
	}
	
	/**
	 * This method checks language inclusion of the first automaton wrt. the
	 * second automaton.
	 *  
	 * @param subset automaton describing the subset language
	 * @param superset automaton describing the superset language
	 * @param stateFactory state factory
	 * @return true iff language is included
	 * @throws AutomataLibraryException thrown by inclusion check
	 */
	private final boolean checkInclusion(
			final INestedWordAutomatonSimple<LETTER, STATE> subset,
			final INestedWordAutomatonSimple<LETTER, STATE> superset,
			final StateFactory<STATE> stateFactory)
				throws AutomataLibraryException {
		return ResultChecker.nwaLanguageInclusion(
				ResultChecker.getOldApiNwa(subset),
				ResultChecker.getOldApiNwa(superset),
				stateFactory) == null;
	}
	
	/**
	 * This method checks whether the input automaton is a DFA.
	 * 
	 * That means the automaton must be deterministic and must not contain any
	 * call and return transitions.
	 * 
	 * @return true iff input automaton is a DFA
	 * @throws AutomataLibraryException thrown by determinism check
	 */
	protected final boolean checkForDfa() throws AutomataLibraryException {
		return (checkForDeterminism() && checkForFiniteAutomaton());
	}
	
	/**
	 * This method checks whether the input automaton is deterministic.
	 * 
	 * @return true iff automaton is deterministic
	 * @throws AutomataLibraryException thrown by determinism check
	 */
	protected final boolean checkForDeterminism()
			throws AutomataLibraryException {
		return new IsDeterministic<LETTER, STATE>(m_operand).
				checkResult(m_operand.getStateFactory());
	}
	
	/**
	 * This method checks whether the automaton is a finite automaton.
	 * That means, it must not contain any call and return transitions.
	 * 
	 * NOTE: Return transitions would not do any harm when no call transitions
	 *       exist, but they are considered bad nevertheless.
	 * 
	 * @return true iff automaton contains no call and return transitions
	 */
	protected final boolean checkForFiniteAutomaton() {
		for (final STATE state : m_operand.getStates()) {
			if (m_operand.callSuccessors(state).iterator().hasNext()) {
				return false;
			}
			if (m_operand.returnSuccessors(state).iterator().hasNext()) {
				return false;
			}
		}
		return true;
	}
	
	/**
	 * This method throws an exception iff the operation should be terminated.
	 * 
	 * @throws OperationCanceledException thrown to enforce termination.
	 */
	protected final void checkForContinuation()
			throws OperationCanceledException {
		if (! NestedWordAutomata.getMonitor().continueProcessing()) {
			throw new OperationCanceledException();
		}
	}
	
	/**
	 * This method computes the capacity size for hash sets and hash maps
	 * given the expected number of elements to avoid resizing. 
	 * 
	 * @param size expected number of elements before resizing
	 * @return the parameter for initializing the hash structure
	 */
	protected final int computeHashCap(int size) {
		return (int) (size * 1.34 + 1);
	}
}
