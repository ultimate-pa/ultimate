package de.uni_freiburg.informatik.ultimate.plugins.generator.impulse;

public class Pair<T,U> {
	private T m_First;
	private U m_Second;
	
	public Pair(T e1, U e2) {
		m_First = e1;
		m_Second = e2;
	}
	
	public T getFirst() {
		return m_First;
	}
	
	public U getSecond() {
		return m_Second;
	}
	
	public boolean equals(Pair<T, U> pair2) {
		if (pair2.getFirst().equals(m_First)) {
			if (pair2.getSecond().equals(m_Second)) {
				return true;
			}
		}
		return false;
	}
}
