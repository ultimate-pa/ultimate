package util;

// In order to keep the original code as much as possible, we
// use the interface of BitSet
public interface IntSet {
	
	IntSet clone();
	
	void andNot(IntSet set);
	
	void and(IntSet set);
	
	void or(IntSet set);
	
	boolean get(int value);
	
	void set(int value);
	
	void clear(int value);
	
	void clear();
	
	boolean isEmpty();
	
	int cardinality();
	
	int hashCode();
	
	String toString();
	
	default boolean overlap(IntSet set) {
		IntSet a = null;
		IntSet b = null;
		
		if(this.cardinality() <= set.cardinality()) {
			a = this;
			b = set;
		}else {
			a = set;
			b = this;
		}
		
		IntIterator iter = a.iterator();
		while(iter.hasNext()) {
			if(b.get(iter.next())) return true; 
		}

		return false;
	}
	
	boolean subsetOf(IntSet set);
	
	boolean contentEq(IntSet set);
	
	Object get();
	
	IntIterator iterator();
		
}
