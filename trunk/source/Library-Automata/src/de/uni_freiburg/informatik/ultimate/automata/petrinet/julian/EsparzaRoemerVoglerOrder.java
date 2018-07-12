package de.uni_freiburg.informatik.ultimate.automata.petrinet.julian;

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
 * @param <C>
 *            place content type
 */
public class EsparzaRoemerVoglerOrder<LETTER, C> implements IOrder<LETTER, C> {
	
	@Override
	public int compare(final Configuration<LETTER, C> c1, final Configuration<LETTER, C> c2) {
		int result = c1.compareTo(c2);
		if (result != 0) {
			return result;
		}
		final Configuration<LETTER, C> min1 = c1.getMin();
		final Configuration<LETTER, C> min2 = c2.getMin();
		result = min1.compareTo(min2);
		if (result != 0) {
			return result;
		}
		final Configuration<LETTER, C> c1withoutMin1 = c1.removeMin();
		final Configuration<LETTER, C> c2withoutMin2 = c2.removeMin();

		// The arguments here are technically no longer Configurations but the lexicographical
		// extension of the order on transitions which is implemented in the compareTo method
		// works on Sets of Events. See 1996TACAS - Esparza,Römer,Vogler, page 13.
		result = compare(c1withoutMin1, c2withoutMin2);
		return result;
	}
}
