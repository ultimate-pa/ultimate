/*
 * Copyright (C) 2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2014-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE Util Library.
 *
 * The ULTIMATE Util Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Util Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Util Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Util Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Util Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.util.datastructures.relation;

import java.util.Map.Entry;

/**
 * Generic Pair.
 *
 * @author Matthias Heizmann
 *
 */
public class Pair<E1, E2> extends BaseTuple<E1, E2> implements Entry<E1, E2> {

	public Pair(final E1 first, final E2 second) {
		super(first, second);
	}

	public E1 getFirst() {
		return mFirstElement;
	}

	public E2 getSecond() {
		return mSecondElement;
	}

	@Override
	public E1 getKey() {
		return getFirst();
	}

	@Override
	public E2 getValue() {
		return getSecond();
	}

	@Override
	public E2 setValue(final E2 value) {
		throw new UnsupportedOperationException("Pair is unmodifiable");
	}
}
