/*
 * Copyright (C) 2009-2012 University of Freiburg
 *
 * This file is part of SMTInterpol.
 *
 * SMTInterpol is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * SMTInterpol is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with SMTInterpol.  If not, see <http://www.gnu.org/licenses/>.
 */
package de.uni_freiburg.informatik.ultimate.smtinterpol.dpll;

import java.util.AbstractQueue;
import java.util.Iterator;

import de.uni_freiburg.informatik.ultimate.smtinterpol.Config;

public class AtomQueue extends AbstractQueue<DPLLAtom> {
	DPLLAtom[] mAtoms;
	int mSize;
	
	public AtomQueue() {
		mAtoms = new DPLLAtom[100];
		mSize = 0;
	}

	@Override
	public Iterator<DPLLAtom> iterator() {
		return new Iterator<DPLLAtom>() {
			int mPos = 0;
			@Override
			public boolean hasNext() {
				return mPos < mSize;
			}
			@Override
			public DPLLAtom next() {
				return mAtoms[mPos++];
			}
			@Override
			public void remove() {
				AtomQueue.this.remove(mAtoms[mPos - 1]);
			}
		};
	}

	@Override
	public int size() {
		return mSize;
	}
	
	private void sink(DPLLAtom atom, int pos) {
		int parent;
		while (pos > 0
		        && mAtoms[parent = (pos - 1) / 2].compareActivityTo(atom) > 0) {
			mAtoms[pos] = mAtoms[parent];
			mAtoms[pos].mAtomQueueIndex = pos;
			pos = parent;
		}
		mAtoms[pos] = atom;
		atom.mAtomQueueIndex = pos;
	}

	@Override
	public boolean offer(DPLLAtom atom) {
		assert atom.mAtomQueueIndex == -1 
			|| mAtoms[atom.mAtomQueueIndex] == atom;
		if (Config.EXPENSIVE_ASSERTS) {
			for (int i = 0; i < mSize; i++) {
				assert mAtoms[i].mAtomQueueIndex == i;
				assert mAtoms[i].mDecideStatus == null;
			}
		}
		if (atom.mAtomQueueIndex != -1) {
			return false;
		}
		if (mSize >= mAtoms.length) {
			final DPLLAtom[] newAtoms = new DPLLAtom[2 * mSize];
			System.arraycopy(mAtoms, 0, newAtoms, 0, mSize);
			mAtoms = newAtoms;
		}
		sink(atom, mSize++);
		return true;
	}

	@Override
	public DPLLAtom peek() {
		assert mSize <= 1 || (mAtoms[0].compareActivityTo(mAtoms[1]) <= 0);
		assert mSize <= 2 || (mAtoms[0].compareActivityTo(mAtoms[2]) <= 0);
		return mAtoms[0];
	}

	@Override
	public DPLLAtom poll() {
		final DPLLAtom atom = mAtoms[0];
		remove(atom);
		return atom;
	}

	@Override
	public boolean contains(Object o) {
		if (!(o instanceof DPLLAtom)) {
			return false;
		}
		assert (((DPLLAtom) o).mAtomQueueIndex == -1
				|| mAtoms[((DPLLAtom) o).mAtomQueueIndex] == o);
		return (((DPLLAtom) o).mAtomQueueIndex != -1);
	}
	
	@Override
	public boolean remove(Object o) {
		if (!(o instanceof DPLLAtom)) {
			return false;
		}
		if (Config.EXPENSIVE_ASSERTS) {
			for (int i = 0; i < mSize; i++) {
				assert mAtoms[i].mAtomQueueIndex == i;
				assert mAtoms[i].mDecideStatus == null || mAtoms[i] == o;
			}
		}
		final DPLLAtom atom = (DPLLAtom) o;
		if (atom.mAtomQueueIndex == -1) {
			return false;
		}
		assert mAtoms[atom.mAtomQueueIndex] == atom;
		
		// remove the element
		int pos = atom.mAtomQueueIndex;
		atom.mAtomQueueIndex = -1;

		// Move children of pos downwards to make a free spot on a leaf.
		while (2 * pos + 2 < mSize) {
			int child = 2 * pos + 1;
			if (mAtoms[child].compareActivityTo(mAtoms[child + 1]) > 0) {
				child++;
			}
			mAtoms[pos] = mAtoms[child];
			mAtoms[pos].mAtomQueueIndex = pos;
			pos = child;
		}
		// Now pos is a free position in the heap that is (or will be) a leaf.
		// All special cases are handled:
		//   pos == m_size-1:  free position at end, nothing to do.
		//   2*pos+1 == m_size-1:  pos has still a single child, but we move
		//                         this into the free spot.
		// in all other cases: move last element to the leaf and let it sink
		// into the tree.
		
		// check if the new free position is at the end.
		if (pos != --mSize) {
			// move the element from the last position to the free leaf
			// and then upwards
			sink(mAtoms[mSize], pos);
		}
		mAtoms[mSize] = null;
		return true;
	}
}
