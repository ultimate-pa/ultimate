package util;

import java.util.Iterator;

class PowerSetPositive implements Iterator<IntSet> {

	private Valuation mValuation;
	
	private final IntSet mSet;
	private final int[] mIntArr;
	
	public PowerSetPositive(IntSet set) {
		assert ! set.isEmpty();
		this.mSet = set;
		mIntArr = new int[mSet.cardinality()];
		int index = 0;
		IntIterator iter = mSet.iterator();
		while(iter.hasNext()) {
			mIntArr[index ++] = iter.next();
		}
		this.mValuation = new Valuation(mSet.cardinality());
	}

	@Override
	public boolean hasNext() {
		int index = mValuation.nextSetBit(0); // whether we have got out of the array
		return index < mValuation.size();
	}

	@Override
	public IntSet next() {
		assert hasNext();
		Valuation val = mValuation.clone();
		mValuation.increment();
		IntSet bits = UtilIntSet.newIntSet();
		for(int n = val.nextSetBit(0); n >= 0 ; n = val.nextSetBit(n + 1)) {
			bits.set(mIntArr[n]);
		}
		return bits;
	}

}
