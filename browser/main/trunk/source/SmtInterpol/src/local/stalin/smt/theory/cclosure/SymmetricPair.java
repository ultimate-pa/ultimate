package local.stalin.smt.theory.cclosure;

public class SymmetricPair<T> {
	T fst, snd;
	public SymmetricPair(T f, T s) {
		fst = f;
		snd = s;
	}
	
	public T getFirst() {
		return fst;
	}
	public T getSecond() {
		return snd;
	}
	
	public int hashCode() {
		return fst.hashCode() + snd.hashCode();
	}
	public boolean equals(Object o) {
		if (o instanceof SymmetricPair) {
			SymmetricPair<?> p = (SymmetricPair<?>) o;
			return (fst.equals(p.fst) && snd.equals(p.snd))
			    || (fst.equals(p.snd) && snd.equals(p.fst));
		}
		return false;
	}
}
