package de.uni_freiburg.informatik.ultimate.automata.petrinet.julian;

import java.util.Comparator;

public abstract class Order<S, C> implements Comparator<Event<S, C>> {
	@Override
	public int compare(Event<S, C> o1, Event<S, C> o2) {
		if (o1 == o2) {
			//s_Logger.info("compared " + o1 + " with itsself.");
			return 0;
		}
		Configuration<S, C> c1 = o1.getLocalConfiguration();
		Configuration<S, C> c2 = o2.getLocalConfiguration();
		assert !(c1.containsAll(c2) && c2.containsAll(c1)) : "Different events with equal local configurations. equals:"
				+ c1.equals(c2);
		int result = compare(c1, c2);

		return result;
	}

	public abstract int compare(Configuration<S, C> o1, Configuration<S, C> o2);
}
