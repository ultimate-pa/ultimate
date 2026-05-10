package de.uni_freiburg.informatik.ultimate.btor;

import de.uni_freiburg.informatik.ultimate.logic.Sort;

public class BtorSort {
	public int size; // if > 0, number of bits. if = 0, represents an array sort
	public BtorSort keySort; // null if bitvector, otherwise is the sort of the key of the array
	public BtorSort valueSort; // null if bitvector, otherwise is the sort of the value of the array

	// constructor for a bitvector sort
	public BtorSort(final int size) {
		this.size = size;
		keySort = null;
		valueSort = null;
	}

	// constructor for an array sort
	public BtorSort(final BtorSort keySort, final BtorSort valueSort) {
		size = 0;
		this.keySort = keySort;
		this.valueSort = valueSort;
	}

	// constructor that takes an SMT sort and creates the corresponding btor sort
	public BtorSort(final Sort sort) {
		if (sort.getName() == "Int") {
			// assume integers are 64 bit
			size = 64;
		} else if (sort.getName() == "Bool") {
			size = 1;
		} else if (sort.getName() == "BitVec") {
			size = Integer.parseInt(sort.getIndices()[0]);
		} else if (sort.getName() == "Array") {
			// combine sizes of all array dimensions
			Sort[] vargs = sort.getArguments();
			int i = new BtorSort(vargs[0]).size;
			while (vargs[1].getName() == "Array") {
				i += new BtorSort(vargs[0]).size;
				vargs = vargs[1].getArguments();
			}
			keySort = new BtorSort(i);
			valueSort = new BtorSort(vargs[1]);
			size = 0;
		} else if (sort.getName() == "Real") {
			throw new UnsupportedOperationException("Reals are not supported by BTOR2 Translation");
		} else if (sort.getName() == "FloatingPoint") {
			throw new UnsupportedOperationException("Floats are not supported by BTOR2 Translation");
		} else if (sort.getName() == "RoundingMode") {
			throw new UnsupportedOperationException("RoundingModes are not supported by BTOR2 Translation");
		} else if (sort.getName() == "myType") {
			throw new UnsupportedOperationException("myTypes are not supported by BTOR2 Translation");
		} else {
			throw new UnsupportedOperationException(
					"Unrecognized sort:" + sort.getName() + ", supported sorts: int, bool, bitvec, and array");
		}

	}

	// check for deep equality
	@Override
	public boolean equals(final Object obj) {
		if (obj == null) {
			return false;
		}
		if (!(obj instanceof BtorSort)) {
			return false;
		}
		final BtorSort other = (BtorSort) obj;
		if (keySort == null) {
			if (other.keySort == null) {
				return size == other.size; // both sorts are bitvectors, so check if sizes are the same
			}
			return false; // we are a bitvector, the other is not, therefore the sorts cannot be equal
		}
		if (other.keySort != null) {
			// both sorts are arrays, so check if the keysort and valuesort sorts are equal
			return keySort.equals(other.keySort) && valueSort.equals(other.valueSort);
		}
		return false; // we are an array, the other is not, therefore the sorts cannot be equal
	}

	public boolean isArray() {
		if (valueSort != null) {
			return true;
		}
		return false;
	}

	@Override
	public int hashCode() {
		return size;
	}
}
