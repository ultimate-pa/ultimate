package de.uni_freiburg.informatik.ultimate.graphvr;

import java.util.stream.Stream;
import java.util.stream.StreamSupport;

public class Converter {

	private static <T> Stream<T> stream(Iterable<T> source) {
		return StreamSupport.stream(source.spliterator(), false);
	}
	
}