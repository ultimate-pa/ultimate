package local.stalin.smt.theory.linar;
import java.util.Comparator;

public class BoundComparator implements Comparator<BoundConstraint> {
	public int compare(BoundConstraint one, BoundConstraint two) {
		return one.mbound.compareTo(two.mbound);
	}
}
