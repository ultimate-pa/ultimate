package de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck;

import de.uni_freiburg.informatik.ultimate.util.HashUtils;

public class Pair<T,U> {
	private final T m_First;
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
	
	private boolean equals(Pair<T, U> pair2) {
		if (pair2.getFirst().equals(m_First)) {
			if (pair2.getSecond().equals(m_Second)) {
				return true;
			}
		}
		return false;
	}
	
	public boolean equals(Object pair2) {
		if (pair2 instanceof Pair<?,?>)
			return this.equals((Pair<T,U>) pair2);
		else 
			return false;
	}
	
	public int hashCode() {
		return HashUtils.hashJenkins(m_First.hashCode(), m_Second.hashCode());
    }
	
	public String toString() {
		return "(" + m_First + "," + m_Second + ")";
	}
}
