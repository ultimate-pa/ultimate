package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder;

import java.util.ArrayList;

public class ShiftedList<String> extends ArrayList<String>{
	
	public int indexOf(String s, int i) {
		
        int index = indexOfRange(s, i, this.size());
        if (index != -1) {
        	return index;
        }
        return indexOfRange(s, 0, i);
    }

    int indexOfRange(Object o, int start, int end) {
        if (o == null) {
            for (int i = start; i < end; i++) {
                if (this.get(i) == null) {
                    return i;
                }
            }
        } else {
            for (int i = start; i < end; i++) {
                if (o.equals(this.get(i))) {
                    return i;
                }
            }
        }
        return -1;
    }
}
