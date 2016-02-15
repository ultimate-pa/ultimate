package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.util;

import java.util.ArrayList;

public class CollectionUtil {

	public static <T> ArrayList<T> singeltonArrayList(T value) {
		ArrayList<T> list = new ArrayList<>();
		list.add(value);
		return list;
	}
}
