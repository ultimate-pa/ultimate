package de.uni_freiburg.informatik.ultimate.smtinterpol.delta;

import de.uni_freiburg.informatik.ultimate.logic.Term;

public class InterpolationTree {
	
	private Term m_Term;
	private InterpolationTree[] m_Children;
	
	private InterpolationTree(Term term, int size) {
		m_Term = term;
		m_Children = new InterpolationTree[size];
	}
	
	private InterpolationTree(InterpolationTree other) {
		m_Term = other.m_Term;
		m_Children = new InterpolationTree[other.m_Children.length];
		System.arraycopy(other.m_Children, 0, m_Children, 0, m_Children.length);
	}
	
	private static InterpolationTree buildTreeHelper(Term[] partition,
			int[] sos, int start) {
		int size = getSize(sos, start);
		InterpolationTree res = new InterpolationTree(partition[start], size);
		// Find children
		int child = start - 1;
		int mystart = sos[start];
		int pos = 0;
		while (child >= mystart) {
			res.m_Children[pos++] = buildTreeHelper(partition, sos, child);
			child = sos[child] - 1;
		}
		return res;
	}
	
	private static int getSize(int[] sos, int start) {
		int mystart = sos[start];
		int size = 1;
		// Find children
		int child = start - 1;
		while (child >= mystart) {
			++size;
			child = sos[child] - 1;
		}
		return size;
	}
	
	public static InterpolationTree buildTree(Term[] partition, int[] sos) {
		return buildTreeHelper(partition, sos, partition.length - 1);
	}
	
	public int size() {
		int size = 1;
		for (InterpolationTree t : m_Children) {
			if (t != null)
				size += t.size();
		}
		return size;
	}
	
	public void dump(Term[] partition, int[] sos) {
		assert (partition.length == sos.length);
		int pos = dumpHelper(partition, sos, 0, 0);
		assert (pos == partition.length);
	}
	
	private int dumpHelper(Term[] partition, int[] sos, int pos, int start) {
		for (InterpolationTree t : m_Children) {
			if (t != null)
				pos = dumpHelper(partition, sos, pos, pos);
		}
		partition[pos] = m_Term;
		sos[pos] = start;
		return pos + 1;
	}
	
	

}
