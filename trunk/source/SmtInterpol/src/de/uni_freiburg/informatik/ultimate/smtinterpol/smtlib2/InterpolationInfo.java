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
package de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2;

import de.uni_freiburg.informatik.ultimate.logic.Term;

public class InterpolationInfo {
	Term[] m_Partitions;
	int[] m_StartOfSubTrees;
	int   m_Size = 0;
	boolean m_IsAndTerm = false;
	
	public InterpolationInfo() {
		m_Partitions = new Term[5];
		m_StartOfSubTrees = new int[5];
	}
	
	private void grow(int minsize) {
		int newsize = 2*m_Partitions.length;
		if (newsize < minsize)
			newsize = minsize + 1;
		Term[] newPartitions = new Term[newsize];
		int[] newStartOfSubTrees = new int[newsize];
		System.arraycopy(m_Partitions, 0, newPartitions, 0, m_Size);
		System.arraycopy(m_StartOfSubTrees, 0, newStartOfSubTrees, 0, m_Size);
		m_Partitions = newPartitions;
		m_StartOfSubTrees = newStartOfSubTrees;
	}
	
	public void makeAndTerm() {
		m_IsAndTerm = true;
	}
	
	public void addParent(Term partition) {
		if (m_Size + 1 >= m_Partitions.length)
			grow(m_Size + 1);
		m_Partitions[m_Size] = partition;
		m_StartOfSubTrees[m_Size] = 0;
		m_Size++;
	}
	
	public void addSibling(InterpolationInfo sibling) {
		if (m_Size + sibling.m_Size >= m_Partitions.length)
			grow(m_Size + sibling.m_Size);
		System.arraycopy(sibling.m_Partitions, 0, m_Partitions, m_Size, sibling.m_Size);
		for (int i = 0; i < sibling.m_Size; i++)
			m_StartOfSubTrees[m_Size + i] = m_Size + sibling.m_StartOfSubTrees[i];
		m_Size += sibling.m_Size;
	}
	
	public Term[] getPartition() {
		if (m_Partitions.length != m_Size) {
			Term[] newPartitions = new Term[m_Size];
			System.arraycopy(m_Partitions, 0, newPartitions, 0, m_Size);
			return newPartitions;
		}
		return m_Partitions;
	}

	public int[] getTreeStructure() {
		if (m_StartOfSubTrees.length != m_Size) {
			int[] newStartOfSubtrees = new int[m_Size];
			System.arraycopy(m_StartOfSubTrees, 0, newStartOfSubtrees, 0, m_Size);
			return newStartOfSubtrees;
		}
		return m_StartOfSubTrees;
	}
	
	public boolean isEmpty() {
		return m_Size == 0;
	}

	public boolean isAndTerm() {
		return m_IsAndTerm;
	}
	
	public boolean isClosedTree() {
		return !m_IsAndTerm && m_Size > 0 && m_StartOfSubTrees[m_Size-1] == 0;
	}
}
