package de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding;

import java.util.Comparator;

/**
 *
 *
 * @author Mehdi Naouar
 *
 * @param <LETTER>
 *            Type of letters from the alphabet used to label transitions
 * @param <PLACE>
 *            place content type
 */
public class DepthBasedOrder<LETTER, PLACE> extends ConfigurationOrder<LETTER, PLACE> {

	final Comparator<Event<LETTER, PLACE>> mDepthIdComparator = new DepthIdComparator();
	@Override
	public int compare(final Configuration<LETTER, PLACE> c1, final Configuration<LETTER, PLACE> c2) {
		int result = c1.compareTo(c2, mDepthIdComparator) ;
		assert result != 0;
		return result;
	}

	class DepthIdComparator implements Comparator<Event<LETTER, PLACE>> {
		// e1 < e2 holds iff
		// depth(e1) < depth(e2)
		// totalOrderId(transition(e1)) < totalOrderId(transition(e2))
		@Override
		public int compare(final Event<LETTER, PLACE> e1, final Event<LETTER, PLACE> e2) {
			final int result = e1.getDepth() - e2.getDepth();
			if (result != 0) {
				return result;
			}
			 return e1.getTotalOrderId() - e2.getTotalOrderId();
		}
	}

	@Override
	public boolean isTotal() {
		return true;
	}
}

