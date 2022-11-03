package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder;

import java.util.ArrayList;

public class ShiftedList<String> extends ArrayList<String> {

	public int indexOf(final String s, final int i) {

		final int index = indexOfRange(s, i, size());
		if (index != -1) {
			return index;
		}
		return indexOfRange(s, 0, i);
	}

	int indexOfRange(final Object o, final int start, final int end) {
		if (o == null) {
			for (int i = start; i < end; i++) {
				if (get(i) == null) {
					return i;
				}
			}
		} else {
			for (int i = start; i < end; i++) {
				if (o.equals(get(i))) {
					return i;
				}
			}
		}
		return -1;
	}
}
