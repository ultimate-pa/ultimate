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

/**
 * An {@link ISleepSetOrder} implementation that maps all states to the same ordering.
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 *
 * @param <S>
 *            The type of states used for sleep set reduction
 * @param <L>
 *            The type of letters
 */
public class ConstantSleepSetOrder<S, L> implements ISleepSetOrder<S, L> {

	private final Map<L, Integer> mLetter2Index = new HashMap<>();

	/**
	 * Creates a new instance.
	 *
	 * @param letters
	 *            All letters in the alphabet. Letters are ordered the same as in this Iterable.
	 */
	public ConstantSleepSetOrder(final Iterable<L> letters) {
		int i = 0;
		for (final L letter : letters) {
			mLetter2Index.put(letter, i);
			i++;
		}
	}

	@Override
	public Comparator<L> getOrder(final S state) {
		return (a, b) -> mLetter2Index.get(a) - mLetter2Index.get(b);
	}
}
