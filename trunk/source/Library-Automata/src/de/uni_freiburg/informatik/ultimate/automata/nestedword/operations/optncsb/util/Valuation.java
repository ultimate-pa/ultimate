package util;

import java.util.BitSet;
import java.util.Iterator;

public class Valuation extends BitSet implements Comparable<Valuation>, Iterable<Integer> {

	/**
	 * should keep the size
	 */
	private static final long serialVersionUID = 1L;
	private int size ;
	
	public Valuation(int size) {
		super(size);
		if(size <= 0) {
			System.err.println("valuation size should be positive number");
			System.exit(-1);
		}
		this.size = size;  // very important to know the size
	}
	
	@Override
	public int size() {
		return size;
	}
	
	public boolean contains(Valuation other) {
		for(int i = other.nextSetBit(0); i >= 0; i ++) {
			if(! get(i)) return false;
		}
		return true;
	}
	
	@Override
	public boolean equals(Object obj) {
		if(obj instanceof BitSet) {
			return this.compareTo((Valuation)obj) == 0;
		}
		return false;
	}
	
	
	@Override
	public Valuation clone() {
		Valuation copy = new Valuation(this.size());
		copy.or(this);
		return copy;
	}
	
	@Override
	public Iterator<Integer> iterator() {
		return new ValuationIterator(this);
	}

	@Override
	public int compareTo(Valuation bits) {
		if(bits.size() > this.size()) return -1;
		if(bits.size() < this.size()) return 1;
		for(int i = 0; i < size(); i ++) {
			if(get(i) && ! bits.get(i)) return 1;
			else if(!get(i) && bits.get(i)) return -1;
		}
		return 0;
	}

	public String toString() {
		StringBuilder builder = new StringBuilder();
		Iterator<Integer> iter = iterator();
		builder.append("{");
		while(iter.hasNext()) {
			builder.append(iter.next());
			if(iter.hasNext()) {
				builder.append(", ");
			}
		}
		builder.append("}");
		return builder.toString();
	}
	
	/** increase a bit */
	protected void increment() {
		int i = this.nextClearBit(0);
		this.clear(0,i);
		this.set(i);
	}
	
	public int toInt() {
		int n = 0;
		for(int i = 0; i < size(); i ++) {
			n += get(i) ? (1 << i) : 0;
		}
		return n;
	}
	
	@Override
	public int hashCode() {
		return toInt();
	}

	public static class ValuationIterator implements Iterator<Integer> {

		private Valuation valuation;
		private int index;
		
		public ValuationIterator(Valuation val) {
			this.valuation = val;
			index = val.nextSetBit(0);
		}
		
		public boolean hasNext() {
			return (index >= 0);
		}
		
		public Integer next() {
			Integer rv = new Integer(index);
			index = valuation.nextSetBit(index + 1);
			return rv;
		}
		
		public void remove() {
			throw new UnsupportedOperationException();
		}
	}
}
