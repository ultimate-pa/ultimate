/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
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
package de.uni_freiburg.informatik.ultimate.util;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Map;
import java.util.concurrent.TimeUnit;

public class Utils {

	/**
	 * Converts a number of bytes to a human readable String containing the byte
	 * number as the highest compatible unit.
	 * 
	 * @param bytes
	 *            A number of bytes
	 * @param si
	 *            true iff SI units should be used (base 1000, without the "i")
	 * @return
	 */
	public static String humanReadableByteCount(final long bytes, final boolean si) {
		final int unit = si ? 1000 : 1024;
		if (bytes < unit) {
			return bytes + " B";
		}
		final int exp = (int) (Math.log(bytes) / Math.log(unit));
		final String pre = (si ? "kMGTPE" : "KMGTPE").charAt(exp - 1) + (si ? "" : "i");
		return String.format("%.1f %sB", bytes / Math.pow(unit, exp), pre);
	}
	
	public static String humanReadableNumber(final long number) {
		final int unit = 1000 ;
		if (number < unit) {
			return Long.toString(number);
		}
		final int exp = (int) (Math.log(number) / Math.log(unit));
		final String pre = String.valueOf(("KMGTPE").charAt(exp - 1));
		return String.format("%.1f %s", number / Math.pow(unit, exp), pre);
	}

	/***
	 * Returns a String representation of a collection by calling toString on
	 * each object in the collection.
	 * 
	 * @param collection
	 * @param delimiter
	 * @return
	 */
	public static String join(final Collection<?> collection, final String delimiter) {
		final StringBuilder builder = new StringBuilder();
		final Iterator<?> iter = collection.iterator();
		while (iter.hasNext()) {
			builder.append(iter.next());
			if (!iter.hasNext()) {
				break;
			}
			builder.append(delimiter);
		}
		return builder.toString();
	}

	/**
	 * Returns a String representation of time as a fraction of the largest
	 * whole unit.
	 * 
	 * I.e. 1001ms becomes 1,001s, 25h become 1,041d.
	 * 
	 * @param time
	 *            The amount of time
	 * @param unit
	 *            The unit of the amount.
	 * @param decimal
	 *            The decimal accurracy of the ouptut.
	 * @return A String with unit symbol.
	 */
	public static String humanReadableTime(final long time, final TimeUnit unit, final int decimal) {
		return humanReadableTime((double) time, unit, decimal);
	}

	/**
	 * Returns a String representation of time as a fraction of the largest
	 * whole unit.
	 * 
	 * I.e. 1001ms becomes 1,001s, 25h become 1,041d.
	 * 
	 * @param time
	 *            The amount of time
	 * @param unit
	 *            The unit of the amount.
	 * @param decimal
	 *            The decimal accurracy of the ouptut.
	 * @return A String with unit symbol.
	 */
	public static String humanReadableTime(final double time, final TimeUnit unit, final int decimal) {
		final String[] units = { "ns", "µs", "ms", "s", "m", "h", "d" };

		switch (unit) {
		case DAYS:
			return String.format("%." + decimal + "f %s", time, units[6]);
		case HOURS:
			if (time > 24) {
				return humanReadableTime(time / 24.0, TimeUnit.DAYS, decimal);
			} else {
				return String.format("%." + decimal + "f %s", time, units[5]);
			}
		case MINUTES:
			if (time > 60) {
				return humanReadableTime(time / 60.0, TimeUnit.HOURS, decimal);
			} else {
				return String.format("%." + decimal + "f %s", time, units[4]);
			}
		case SECONDS:
			if (time > 60) {
				return humanReadableTime(time / 60.0, TimeUnit.MINUTES, decimal);
			} else {
				return String.format("%." + decimal + "f %s", time, units[3]);
			}
		case MILLISECONDS:
			if (time > 1000) {
				return humanReadableTime(time / 1000.0, TimeUnit.SECONDS, decimal);
			} else {
				return String.format("%." + decimal + "f %s", time, units[2]);
			}
		case MICROSECONDS:
			if (time > 1000) {
				return humanReadableTime(time / 1000.0, TimeUnit.MILLISECONDS, decimal);
			} else {
				return String.format("%." + decimal + "f %s", time, units[1]);
			}
		case NANOSECONDS:
			if (time > 1000) {
				return humanReadableTime(time / 1000.0, TimeUnit.MICROSECONDS, decimal);
			} else {
				return String.format("%." + decimal + "f %s", time, units[0]);
			}
		default:
			throw new UnsupportedOperationException(unit + " TimeUnit not yet implemented");
		}
	}
	
	
	/**
	 * Filter Collection to all elements that are subclasses of clazz.
	 */
	@SuppressWarnings("unchecked")
	public static <E> Collection<E> filter(final Collection<?> iterable, final Class<E> clazz) {
		final ArrayList<E> filteredList = new ArrayList<E>();
		for (final Object e: iterable) {
			if (clazz.isAssignableFrom(e.getClass())) {
				filteredList.add((E) e);
			}
		}
		return filteredList;
	}
	
	/**
	 * Construct a new HashSet that contains the elements of a given Iterable.
	 */
	public static <E> HashSet<E> constructHashSet(final Iterable<E> iterable) {
		final HashSet<E> result = new HashSet<E>();
		for (final E element : iterable) {
			result.add(element);
		}
		return result;
	}
	
	/**
	 * @return a new HashMap that contains all key-value pairs of map whose
	 * key is contained in filter.
	 */
	public static <K,V> HashMap<K,V> constructFilteredMap(final Map<K,V> map, final Collection<K> filter) {
		final HashMap<K,V> result = new HashMap<>();
		for (final K key : filter) {
			final V value = map.get(key);
			if (value != null) {
				result.put(key, value);
			}
		}
		return result;
	}
}
