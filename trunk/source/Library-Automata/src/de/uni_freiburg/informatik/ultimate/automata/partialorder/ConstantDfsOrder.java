/*
 * Copyright (C) 2020 Marcel Ebbinghaus
 * Copyright (C) 2020 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2020 University of Freiburg
 *
 * This file is part of the ULTIMATE Automata Library.
 *
 * The ULTIMATE Automata Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Automata Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Automata Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Automata Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Automata Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.automata.partialorder;

import java.util.Comparator;
import java.util.HashMap;
import java.util.Map;
import java.util.function.Function;

/**
 * An {@link IDfsOrder} implementation that maps all states to the same ordering.
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 *
 * @param <S>
 *            The type of states used for sleep set reduction
 * @param <L>
 *            The type of letters
 */
public class ConstantDfsOrder<L, S> implements IDfsOrder<L, S> {
	private final Comparator<L> mComparator;

	/**
	 * Create a new instance where every state uses the given order.
	 *
	 * @param comparator
	 *            The order to use for every state, as {@link Comparator}
	 */
	public ConstantDfsOrder(final Comparator<L> comparator) {
		mComparator = comparator;
	}

	@Override
	public Comparator<L> getOrder(final S state) {
		return mComparator;
	}

	@Override
	public boolean isPositional() {
		return false;
	}

	public static <L, S, U extends Comparable<U>> ConstantDfsOrder<L, S> comparing(final Function<L, U> keyExtractor) {
		return new ConstantDfsOrder<>(Comparator.comparing(keyExtractor));
	}

	public static <L, S, U> ConstantDfsOrder<L, S> comparing(final Function<L, U> keyExtractor,
			final Comparator<U> comparator) {
		return new ConstantDfsOrder<>(Comparator.comparing(keyExtractor, comparator));
	}

	public static <L, S> ConstantDfsOrder<L, S> byHashCode() {
		return comparing(Object::hashCode);
	}

	public static <L, S> ConstantDfsOrder<L, S> fromIterable(final Iterable<L> letters) {
		final Map<L, Integer> letter2Index = new HashMap<>();
		int i = 0;
		for (final L letter : letters) {
			letter2Index.put(letter, i);
			i++;
		}
		return comparing(letter2Index::get);
	}
}
