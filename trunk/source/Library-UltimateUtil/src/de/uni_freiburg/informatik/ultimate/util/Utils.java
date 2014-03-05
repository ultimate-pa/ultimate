package de.uni_freiburg.informatik.ultimate.util;

import java.util.Collection;
import java.util.Iterator;
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
	public static String humanReadableByteCount(long bytes, boolean si) {
		int unit = si ? 1000 : 1024;
		if (bytes < unit)
			return bytes + " B";
		int exp = (int) (Math.log(bytes) / Math.log(unit));
		String pre = (si ? "kMGTPE" : "KMGTPE").charAt(exp - 1) + (si ? "" : "i");
		return String.format("%.1f %sB", bytes / Math.pow(unit, exp), pre);
	}

	/***
	 * Returns a String representation of a collection by calling toString on
	 * each object in the collection.
	 * 
	 * @param collection
	 * @param delimiter
	 * @return
	 */
	public static String join(Collection<?> collection, String delimiter) {
		StringBuilder builder = new StringBuilder();
		Iterator<?> iter = collection.iterator();
		while (iter.hasNext()) {
			builder.append(iter.next());
			if (!iter.hasNext()) {
				break;
			}
			builder.append(delimiter);
		}
		return builder.toString();
	}

	public static String humanReadableTime(long time, TimeUnit unit, int decimal) {
		String[] units = { "ns", "µs", "ms", "s", "m", "h", "d" };

		int exp = 6;

		if (unit == TimeUnit.DAYS) {
			return String.format("%." + decimal + "f %s", time, units[exp]);
		}

		if (unit == TimeUnit.HOURS) {
		}

		return "";
	}

	private double NanosToSeconds(long time) {
		int factor = 1000;
		int exp = (int) (Math.log(time) / Math.log(factor));
		return ((double) time) / Math.pow(factor, exp);
	}

}
