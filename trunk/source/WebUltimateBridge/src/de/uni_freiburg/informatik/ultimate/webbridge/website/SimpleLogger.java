package de.uni_freiburg.informatik.ultimate.webbridge.website;

import java.text.SimpleDateFormat;
import java.util.Calendar;

public final class SimpleLogger {

	private SimpleLogger() {
		// singleton logger does not need constructor
	}

	public static void log(final String message) {
		if (message != null) {
			final String timestamp =
					new SimpleDateFormat("yyyy-MM-dd_HH-mm-ss-SSS").format(Calendar.getInstance().getTime());
			System.out.println("[" + timestamp + "] " + message);
		}
	}

	public static void log(final Object o) {
		if (o != null) {
			log(o.toString());
		}
	}
}
