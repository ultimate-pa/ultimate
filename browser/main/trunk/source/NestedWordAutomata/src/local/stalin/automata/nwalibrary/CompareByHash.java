package local.stalin.automata.nwalibrary;

import java.util.Comparator;

public class CompareByHash implements Comparator<Object> {
	@Override
	public int compare(Object o1, Object o2) {
		if (o1.equals(o2))
			return 0;
		return o1.hashCode() - o2.hashCode();
	}
	
	public static CompareByHash instance = new CompareByHash();
}
