package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.minimization;

import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomaton;

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
	protected AMinimizeIncremental(final String name,
			final INestedWordAutomaton<LETTER, STATE> operand,
			final Interrupt interrupt) {
		super(name, operand);
		m_interrupt = interrupt;
		assert ((m_interrupt == null) || (! m_interrupt.getStatus())) :
			"The interrupt tells to terminate right at the beginning.";
	}
}
