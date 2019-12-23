package de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding;

/**
 * Order presented by Esparza, Römer, Vogler in 1996 TACAS,
 * <a href="http://citeseerx.ist.psu.edu/viewdoc/summary?doi=10.1.1.1.9584"> An
 * improvement of McMillan's unfolding algorithm</a>, definition 4.1.
 *
 * @author Julian Jarecki (jareckij@informatik.uni-freiburg.de)
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @author schaetzc@tf.uni-freiburg.de
 * @author Mehdi Naouar
 *
 * @param <LETTER>
 *            Type of letters from the alphabet used to label transitions
 * @param <PLACE>
 *            place content type
 */
public class EsparzaRoemerVoglerOrder<LETTER, PLACE> extends EventOrder<LETTER, PLACE> {

	@Override
	public int compare(Configuration<LETTER, PLACE> c1, Configuration<LETTER, PLACE> c2) {
		// we compare first the sizes of C1 and C2; if they are equal, we compare ϕ(C1)
		// and ϕ(C2);
		int result = c1.compareTo(c2);
		if (result != 0) {
			return result;
		}

		// if they are equal, we compare FC1 and FC2 by comparing their Foata normal
		// forms FC1 = C11...C1n1 and
		// FC2 =C21...C2n2 with respect to the order <<
		// See Section 6 of the following publication.
		// 2002FMSD - Esparza,Römer,Vogler - An Improvement of McMillan's Unfolding Algorithm
		while (true) {
			// We compute in the iteration i, min1 = C1i and min2 = C2i and
			// compare lexicographically ϕ(min1) and ϕ(min2) with respect to the order <<
			final Configuration<LETTER, PLACE> min1 = c1.getMin();
			final Configuration<LETTER, PLACE> min2 = c2.getMin();
			result = min1.compareTo(min2);
			if (result != 0) {
				return result;
			}
			c1 = c1.removeMin();
			c2 = c2.removeMin();
		}
	}

	@Override
	public boolean isTotal() {
		return true;
	}
}
