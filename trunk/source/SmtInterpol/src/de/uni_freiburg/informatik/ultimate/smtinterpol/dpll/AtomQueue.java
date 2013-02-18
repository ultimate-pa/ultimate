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
	DPLLAtom[] m_atoms;
	int m_size;
	
	public AtomQueue() {
		m_atoms = new DPLLAtom[100];
		m_size = 0;
	}

	@Override
	public Iterator<DPLLAtom> iterator() {
		return new Iterator<DPLLAtom>() {
			int pos = 0;
			public boolean hasNext() {
				return pos < m_size;
			}
			public DPLLAtom next() {
				return m_atoms[pos++];
			}
			public void remove() {
				AtomQueue.this.remove(m_atoms[pos-1]);
			}
		};
	}

	@Override
	public int size() {
		return m_size;
	}
	
	private void sink(DPLLAtom atom, int pos) {
		int parent;
		while (pos > 0 && m_atoms[parent = (pos-1)/2].compareActivityTo(atom) > 0) {
			m_atoms[pos] = m_atoms[parent];
			m_atoms[pos].m_atomQueueIndex = pos;
			pos = parent;
		}
		m_atoms[pos] = atom;
		atom.m_atomQueueIndex = pos;
	}

	@Override
	public boolean offer(DPLLAtom atom) {
		assert atom.m_atomQueueIndex == -1 
			|| m_atoms[atom.m_atomQueueIndex] == atom;
		if (Config.EXPENSIVE_ASSERTS) {
			for (int i = 0; i < m_size; i++) {
				assert m_atoms[i].m_atomQueueIndex == i;
				assert m_atoms[i].decideStatus == null;
			}
		}
		if (atom.m_atomQueueIndex != -1)
			return false;
		if (m_size >= m_atoms.length) {
			DPLLAtom[] newAtoms = new DPLLAtom[2*m_size];
			System.arraycopy(m_atoms, 0, newAtoms, 0, m_size);
			m_atoms = newAtoms;
		}
		sink(atom, m_size++);
		return true;
	}

	@Override
	public DPLLAtom peek() {
		assert m_size <= 1 || (m_atoms[0].compareActivityTo(m_atoms[1]) <= 0);
		assert m_size <= 2 || (m_atoms[0].compareActivityTo(m_atoms[2]) <= 0);
		return m_atoms[0];
	}

	@Override
	public DPLLAtom poll() {
		DPLLAtom atom = m_atoms[0];
		remove(atom);
		return atom;
	}

	@Override
	public boolean contains(Object o) {
		if (!(o instanceof DPLLAtom))
			return false;
		assert (((DPLLAtom) o).m_atomQueueIndex == -1
				|| m_atoms[((DPLLAtom) o).m_atomQueueIndex] == o);
		return (((DPLLAtom) o).m_atomQueueIndex != -1);
	}
	
	@Override
	public boolean remove(Object o) {
		if (!(o instanceof DPLLAtom))
			return false;
		if (Config.EXPENSIVE_ASSERTS) {
			for (int i = 0; i < m_size; i++) {
				assert m_atoms[i].m_atomQueueIndex == i;
				assert m_atoms[i].decideStatus == null || m_atoms[i] == o;
			}
		}
		DPLLAtom atom = (DPLLAtom) o;
		if (atom.m_atomQueueIndex == -1)
			return false;
		assert m_atoms[atom.m_atomQueueIndex] == atom;
		
		// remove the element
		int pos = atom.m_atomQueueIndex;
		atom.m_atomQueueIndex = -1;

		// Move children of pos downwards to make a free spot on a leaf.
		while (2*pos+2 < m_size) {
			int child = 2*pos + 1;
			if (m_atoms[child].compareActivityTo(m_atoms[child+1]) > 0)
				child++;
			m_atoms[pos] = m_atoms[child];
			m_atoms[pos].m_atomQueueIndex = pos;
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
		if (pos != --m_size) {
			// move the element from the last position to the free leaf
			// and then upwards
			sink(m_atoms[m_size], pos);
		}
		m_atoms[m_size] = null;
		return true;
	}
}
