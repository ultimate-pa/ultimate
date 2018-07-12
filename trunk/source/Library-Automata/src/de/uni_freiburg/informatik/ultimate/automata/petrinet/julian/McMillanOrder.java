package de.uni_freiburg.informatik.ultimate.automata.petrinet.julian;

/**
 * Naive order used by McMillan.
 * 
 * @author Julian Jarecki (jareckij@informatik.uni-freiburg.de)
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * 
 * @param <LETTER>
 *            Type of letters from the alphabet used to label transitions
 * @param <C>
 *            place content type
 */
public class McMillanOrder<LETTER, C> implements IOrder<LETTER, C> {

	@Override
	public int compare(final Configuration<LETTER, C> o1, final Configuration<LETTER, C> o2) {
		return o1.size() - o2.size();
	}
	
}
