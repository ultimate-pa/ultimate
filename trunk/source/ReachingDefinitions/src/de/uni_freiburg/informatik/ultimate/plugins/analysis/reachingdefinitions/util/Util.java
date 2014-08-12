package de.uni_freiburg.informatik.ultimate.plugins.analysis.reachingdefinitions.util;


public class Util {

	public static <T> String prettyPrintIterable(Iterable<T> remaining, ElemToString<T> converter) {
		StringBuilder sb = new StringBuilder();
		for (T e : remaining) {
			sb.append(converter.toString(e)).append(", ");
		}
		sb.delete(sb.length() - 2, sb.length());
		return sb.toString();
	}
	
	public static String repeat(int c, String r) {
		String rtr = "";
	
		while (c > 0) {
			rtr = rtr + r;
			c--;
		}
		return rtr;
	}
	
	public static <T> ElemToString<T> createHashCodePrinter(){
		return new ElemToString<T>() {
			@Override
			public String toString(T elem) {
				return String.valueOf(elem.hashCode());
			}
		};
	}
	
	public interface ElemToString<E>{
		public String toString(E elem);
	}

}


