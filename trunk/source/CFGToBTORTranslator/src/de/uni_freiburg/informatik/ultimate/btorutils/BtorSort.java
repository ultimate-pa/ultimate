package de.uni_freiburg.informatik.ultimate.btorutils;

import de.uni_freiburg.informatik.ultimate.logic.Sort;

public class BtorSort {
	int size;
	BtorSort keySort;
	BtorSort valueSort;

	public BtorSort(final int size) {
		this.size = size;
		keySort = null;
		valueSort = null;
	}

	public BtorSort(final BtorSort keySort, final BtorSort valueSort) {
		size = 0;
		this.keySort = null;
		this.valueSort = null;
	}

	public BtorSort(final Sort sort) {
		if (sort.getName() == "Int") {
			size = 64;
		} else if (sort.getName() == "Bool") {
			size = 1;
		} else if (sort.getName() == "BitVec") {
			size = Integer.parseInt(sort.getIndices()[0]);
		} else if (sort.getName() == "Array") {
			keySort = new BtorSort(sort.getArguments()[0]);
			valueSort = new BtorSort(sort.getArguments()[1]);
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
			throw new UnsupportedOperationException("Unrecognized sort, supported sorts: int, bool, bitvec, and array");
		}

	}

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
				return size == other.size;
			}
			return false;
		}
		if (other.keySort != null) {
			return keySort.equals(other.keySort) && valueSort.equals(other.valueSort);
		}
		return false;
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
