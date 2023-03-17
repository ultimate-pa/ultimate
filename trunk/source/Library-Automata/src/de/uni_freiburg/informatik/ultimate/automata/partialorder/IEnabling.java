package de.uni_freiburg.informatik.ultimate.automata.partialorder;

import java.util.Set;

/**
 * interface for membranes used in the dynamic partial order reduction algorithm
 *
 * @author Tilo Heep
 *
 * @param <LETTER>
 *            The type of letters which are in the enabling set
 * @param <STATE>
 *            The type of states in which the set of letters is an enabling set
 */
public interface IEnabling<LETTER, STATE> {

	/**
	 * A function that computes an EnablingSet(a, q) / the function f_a(q) which is the Enabling set to enable a from
	 * state q
	 *
	 * @param q
	 *            is the state from which the letter should be enabled
	 * @return a set of letters that is a subset of enabled letters in state q with the property that if there exists a
	 *         way to enable letter "a" one must first read a letter from the enabling set
	 */
	Set<LETTER> getEnablingSet(STATE q, LETTER a);
}
