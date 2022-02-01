/*
 * Copyright (C) 2018 Claus Schaetzle (schaetzc@tf.uni-freiburg.de)
 * Copyright (C) 2018 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.util.datastructures;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.function.Function;

/**
 * Set operations, for instance union and intersection. These methods work with every type of Collection, not only sets.
 * In case the inputs contain duplicates, the output may or may not contain duplicates too.
 *
 * @author schaetzc@tf.uni-freiburg.de
 * @deprecated Merge with {@link DataStructureUtils}
 */
@Deprecated
public final class SetOperations {

	private SetOperations() {
		// No need for objects of this class.
		// Class contains only static methods.
	}

	private static <E> Collection<E> smallestCollection(final Collection<E>[] collections) {
		Collection<E> min = null;
		for (final Collection<E> collection : collections) {
			if (min == null || collection.size() < min.size()) {
				min = collection;
			}
		}
		return min;
	}

	private static <E, RESULT extends Collection<E>> RESULT
			intersectionIntern(final Function<Collection<E>, RESULT> smallerSetCopier, final Collection<E>[] operands) {
		final Collection<E> min = smallestCollection(operands);
		final RESULT result = smallerSetCopier.apply(min);
		for (final Collection<E> operand : operands) {
			if (operand != min) {
				result.retainAll(operand);
			}
		}
		return result;
	}

	@SafeVarargs
	public static <E> Set<E> intersection(final Collection<E>... operands) {
		return intersectionIntern(HashSet::new, operands);
	}

	@SafeVarargs
	public static <E> List<E> intersectionList(final Collection<E>... operands) {
		return intersectionIntern(ArrayList::new, operands);
	}

	private static <E, RESULT extends Collection<E>> RESULT differenceIntern(
			final Function<Collection<E>, RESULT> minuendCopier, final Collection<E> minuend,
			final Collection<E> subtrahend) {
		final RESULT result = minuendCopier.apply(minuend);
		result.removeAll(subtrahend);
		return result;
	}

	public static <E> Set<E> difference(final Collection<E> minuend, final Collection<E> subtrahend) {
		return differenceIntern(HashSet::new, minuend, subtrahend);
	}

	public static <E> List<E> differenceList(final Collection<E> minuend, final Collection<E> subtrahend) {
		return differenceIntern(ArrayList::new, minuend, subtrahend);
	}

	public static <E> boolean disjoint(final Collection<E> set1, final Collection<E> set2) {
		return Collections.disjoint(set1, set2);
	}

	public static <E> boolean intersecting(final Collection<E> set1, final Collection<E> set2) {
		return !Collections.disjoint(set1, set2);
	}
}
