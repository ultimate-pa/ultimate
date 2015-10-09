package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.deltaDebug;

import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomaton;

/**
 * Executes the respective method which should be debugged and compares to the
 * designated error.
 * 
 * Usage:
 * Initially, the error which is to be expected is stored in order to be able to
 * compare to its concrete type during the search later on.
 * The {@link #execute(INestedWordAutomaton)} method
 * must be overwritten to run the designated method accordingly.
 * 
 * The architecture allows for very general testing features such as additional
 * pre- and post-processing, but comes with the price that this class must be
 * implemented for each method anew.
 * 
 * @author Christian Schilling <schillic@informatik.uni-freiburg.de>
 */
public abstract class ATester<LETTER, STATE> {
	final Throwable m_throwable;
	
	public ATester(final Throwable throwable) {
		this.m_throwable = throwable;
	}
	
	/**
	 * Tests whether an input still produces an error.
	 * 
	 * @param automaton input automaton
	 * @return true iff an error of the original error type (exact) occurred
	 */
	public boolean test(final INestedWordAutomaton<LETTER, STATE> automaton) {
		try {
			execute(automaton);
		} catch (final Throwable throwable) {
			return m_throwable.getClass().isInstance(throwable) &&
					throwable.getClass().isInstance(m_throwable);
		}
		return false;
	}
	
	/**
	 * Executes the method to be tested on the given automaton.
	 * 
	 * @param automaton input automaton
	 * @throws any type of throwable
	 */
	public abstract void execute(
		final INestedWordAutomaton<LETTER, STATE> automaton)
			throws Throwable;
	
	@Override
	public String toString() {
		final StringBuilder b = new StringBuilder();
		b.append(this.getClass().getSimpleName());
		b.append(" with exception type '");
		b.append(m_throwable.getClass().getSimpleName());
		b.append("'");
		return b.toString();
	}
}