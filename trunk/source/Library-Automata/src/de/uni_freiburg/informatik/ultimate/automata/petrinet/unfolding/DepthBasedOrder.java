package de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding;

import java.util.Comparator;
import java.util.List;
import java.util.stream.Collectors;

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
public class DepthBasedOrder<LETTER, PLACE> extends EventOrder<LETTER, PLACE> {

	final Comparator<Event<LETTER, PLACE>> mDepthIdComparator = new DepthIdComparator();
	@Override
	public int compare(Configuration<LETTER, PLACE> c1, Configuration<LETTER, PLACE> c2) {	
		
		// we compare first the sizes of C1 and C2;
		int result = c1.size() - c2.size();
		if (result != 0) {
			return result;
		}
		
		//the following comparison is optional: I am trying to find out if we can use a heuristic based on the depth
		//to reduce the overall number of events of the computed complete finite prefix
		result = c2.getDepth() - c1.getDepth();
		if (result != 0) {
			return result;
		}
		
		// We sort the local configuration using the DepthIdComparator: see the compare method of the comparator bellow
		List<Event<LETTER, PLACE>> c1Sorted = c1.getSortedConfiguration(mDepthIdComparator);
		List<Event<LETTER, PLACE>> c2Sorted = c2.getSortedConfiguration(mDepthIdComparator);
		for (int i = 0; i< c1.size(); i++) {
			result = mDepthIdComparator.compare(c1Sorted.get(i), c2Sorted.get(i));
			if (result != 0) {
				return result;
			}
		}
		return 0;
	}
	
	class DepthIdComparator implements Comparator<Event<LETTER, PLACE>> {
		// e1 < e2 holds iff
		// depth(e1) < depth(e2)
		// totalOrderId(transition(e1)) < totalOrderId(transition(e2))
		@Override
		public int compare(Event<LETTER, PLACE> e1, Event<LETTER, PLACE> e2) {
			int result = e1.getDepth() - e2.getDepth();
			if (result != 0) {
				return result;
			}
			 return e1.getTotalOrderId() - e2.getTotalOrderId();
		}
	}
}

