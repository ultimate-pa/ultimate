package de.uni_freiburg.informatik.ultimate.util;

public class ExceptionUtils {
	public static String getStackTrace(Throwable t) {
		StringBuilder sb = new StringBuilder();
		for (StackTraceElement elem : t.getStackTrace()) {
			sb.append(String.format("%s%n", elem.toString()));
		}
		return sb.toString();
	}
}
