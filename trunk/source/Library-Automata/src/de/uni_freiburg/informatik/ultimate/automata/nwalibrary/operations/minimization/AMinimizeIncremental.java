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

import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;

/**
 * This is the superclass of all incremental minimization classes.
 * 
 * The idea is to use threading. One thread controls the state of the interrupt
 * and one thread runs the minimization. This is the caller's job.
 * 
 * Whenever the first thread decides to stop the minimization, it informs the
 * interrupt. The minimization is expected to regularly check the state of the
 * interrupt and if it should terminate it stops its normal execution and only
 * constructs the result from the information it has gathered so far.
 * 
 * @author Christian
 */
public abstract class AMinimizeIncremental<LETTER, STATE>
		extends AMinimizeNwa<LETTER, STATE> {
	/**
	 * The interrupt.
	 */
	protected final Interrupt m_interrupt;
	
	/**
	 * This constructor should be called by all subclasses and only by them.
	 * 
	 * @param name operation name
	 * @param operand input automaton
	 * @param interrupt interrupt
	 */
	protected AMinimizeIncremental(final StateFactory<STATE> stateFactory,
			final String name,
			final INestedWordAutomaton<LETTER, STATE> operand,
			final Interrupt interrupt) {
		super(stateFactory, name, operand);
		m_interrupt = interrupt;
		assert ((m_interrupt == null) || (! m_interrupt.getStatus())) :
			"The interrupt tells to terminate right at the beginning.";
	}
}
