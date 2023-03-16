package de.uni_freiburg.informatik.ultimate.automata.partialorder.disabling;


/**
 * interface for the disabling relation used in the dynamic partial order reduction algorithm
 *
 * @author Tilo Heep
 *
 * @param <LETTER>
 *            The type of letters in the disabling relation
 */
public interface IDisabling<LETTER> {

	/**
	 * 
	 * @param a: letter that might disable b
	 * @param b: letter that might get disabled by a
	 * @return true if (a,b) in Delta / a disables b
	 *         false if (a,b) not in Delta / a does not disable b
	 */
	boolean disables(LETTER a, LETTER b);
}

