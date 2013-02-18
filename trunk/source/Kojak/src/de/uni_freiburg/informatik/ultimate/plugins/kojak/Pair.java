package de.uni_freiburg.informatik.ultimate.plugins.kojak;

public class Pair<T,U> {
	private T m_Entry1;
	private U m_Entry2;
	
	public Pair(T e1, U e2) {
		m_Entry1 = e1;
		m_Entry2 = e2;
	}
	
	public T getEntry1() {
		return m_Entry1;
	}
	
	public U getEntry2() {
		return m_Entry2;
	}
	
	public boolean equals(Pair<T, U> pair2) {
		if (pair2.getEntry1().equals(m_Entry1)) {
			if (pair2.getEntry2().equals(m_Entry2)) {
				return true;
			}
		}
		return false;
	}
}
