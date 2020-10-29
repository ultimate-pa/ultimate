package de.uni_freiburg.informatik.ultimate.automata.partialorder;

import java.util.Comparator;
import java.util.HashMap;
import java.util.Map;

public class ConstantSleepSetOrder<S, L> implements ISleepSetOrder<S, L> {

	private final Map<L, Integer> letter2Index = new HashMap<>();

	@Override
	public Comparator<L> getOrder(final S state) {
		return (a, b) -> letter2Index.get(a) - letter2Index.get(b);
	}

	public ConstantSleepSetOrder(final Iterable<L> letters) {
		int i = 0;
		for (final L letter : letters) {
			letter2Index.put(letter, i);
			i++;
		}
	}
}
