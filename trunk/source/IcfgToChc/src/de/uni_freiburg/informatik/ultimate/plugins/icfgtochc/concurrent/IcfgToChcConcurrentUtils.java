package de.uni_freiburg.informatik.ultimate.plugins.icfgtochc.concurrent;

/**
 *
 * @author Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 *
 */
public class IcfgToChcConcurrentUtils {
	private IcfgToChcConcurrentUtils() {
	}

	public static String getReadableString(final Object obj) {
		return obj.toString().replaceAll("Thread\\d+of\\d+ForFork\\d+", "");
	}
}
