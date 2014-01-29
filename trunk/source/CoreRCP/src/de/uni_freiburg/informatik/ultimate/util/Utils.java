package de.uni_freiburg.informatik.ultimate.util;

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
		String pre = (si ? "kMGTPE" : "KMGTPE").charAt(exp - 1)
				+ (si ? "" : "i");
		return String.format("%.1f %sB", bytes / Math.pow(unit, exp), pre);
	}

}
