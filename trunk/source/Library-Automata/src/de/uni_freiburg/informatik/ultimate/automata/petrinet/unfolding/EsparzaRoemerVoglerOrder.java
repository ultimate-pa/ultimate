package de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding;

/**
 * Order presented by Esparza, Römer, Vogler in 1996 TACAS,
 * <a href="http://citeseerx.ist.psu.edu/viewdoc/summary?doi=10.1.1.1.9584">
 * An improvement of McMillan's unfolding algorithm</a>, definition 4.1.
 * 
 * @author Julian Jarecki (jareckij@informatik.uni-freiburg.de)
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @author schaetzc@tf.uni-freiburg.de
 * 
 * @param <LETTER>
 *            Type of letters from the alphabet used to label transitions
 * @param <PLACE>
 *            place content type
 */
public class EsparzaRoemerVoglerOrder<LETTER, PLACE> implements IOrder<LETTER, PLACE> {
	
	@Override
	public int compare(Configuration<LETTER, PLACE> c1, Configuration<LETTER, PLACE> c2) {
		while (true) {
			int result = c1.compareTo(c2);
			if (result != 0) {
				return result;
			}
			final Configuration<LETTER, PLACE> min1 = c1.getMin();
			final Configuration<LETTER, PLACE> min2 = c2.getMin();
			result = min1.compareTo(min2);
			if (result != 0) {
				return result;
			}
			// The arguments here are technically no longer Configurations but the lexicographical
			// extension of the order on transitions which is implemented in the compareTo method
			// works on Sets of Events. See 1996TACAS - Esparza,Römer,Vogler, page 13.
			c1 = c1.removeMin();
			c2 = c2.removeMin();
		}
	}
}
