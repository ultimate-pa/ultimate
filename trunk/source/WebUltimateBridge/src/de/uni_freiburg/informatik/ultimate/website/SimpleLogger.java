package de.uni_freiburg.informatik.ultimate.website;

import java.text.SimpleDateFormat;
import java.util.Calendar;

public class SimpleLogger {
	public static void log(String message) {
		if (message != null) {
			String timestamp = new SimpleDateFormat("yyyy-MM-dd_HH-mm-ss-SSS").format(Calendar.getInstance().getTime());
			timestamp = "[" + timestamp + "] ";
			message = timestamp + message;
			System.out.println(message);
		}
	}

	public static void log(Object o) {
		if (o != null) {
			log(o.toString());
		}
	}
}
