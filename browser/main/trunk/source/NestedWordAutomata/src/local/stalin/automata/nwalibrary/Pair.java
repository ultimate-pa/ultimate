package local.stalin.automata.nwalibrary;

import java.util.Comparator;


// Because the Java people couldn't figure out how to write this class, we have to do it
public class Pair<A, B> implements Comparable<Pair<A, B>> {
	public A fst;
	public B snd;
	// These are public. So what?
	
	public Pair(A first, B second) {
		this.fst = first;
		this.snd = second;
	}

	public int compareTo(Pair<A, B> pair) {
		// To make things easier, compare fst and snd by hash, so they don't have to be
		// comparable.
		Comparator<Object> comp = CompareByHash.instance;
		
		int compFst = comp.compare(this.fst, pair.fst);
		if (compFst != 0)
			return compFst;
		else
			return comp.compare(this.snd, pair.snd);
	}
	
	/* (non-Javadoc)
	 * @see java.lang.Object#hashCode()
	 */
	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((fst == null) ? 0 : fst.hashCode());
		result = prime * result + ((snd == null) ? 0 : snd.hashCode());
		return result;
	}

	/* (non-Javadoc)
	 * @see java.lang.Object#equals(java.lang.Object)
	 */
	@SuppressWarnings("unchecked")
	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj == null)
			return false;
		if (getClass() != obj.getClass())
			return false;
		Pair<A, B> other = (Pair<A, B>) obj;
		if (fst == null) {
			if (other.fst != null)
				return false;
		} else if (!fst.equals(other.fst))
			return false;
		if (snd == null) {
			if (other.snd != null)
				return false;
		} else if (!snd.equals(other.snd))
			return false;
		return true;
	}
}
