package de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.preprocessors.rewriteArrays;

/**
 * We call a multiset of two elements a twoelton.
 * @author Matthias Heizmann
 *
 * @param <E>
 */
public class Twoelton<E> {
	
	
	private final E m_OneElement;
	private final E m_OtherElement;
	public Twoelton(E oneElement, E otherElement) {
		super();
		if (oneElement == null || otherElement == null) {
			throw new NullPointerException();
		}
		m_OneElement = oneElement;
		m_OtherElement = otherElement;
	}
	public E getOneElement() {
		return m_OneElement;
	}
	public E getOtherElement() {
		return m_OtherElement;
	}
	public E[] toArray() {
		E[] result = (E[]) new Object[] { m_OneElement, m_OtherElement};
		return result;
	}
	
	@Override
	public int hashCode() {
		return m_OneElement.hashCode() + m_OtherElement.hashCode();
	}
	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj == null)
			return false;
		if (getClass() != obj.getClass())
			return false;
		Twoelton<E> other = (Twoelton) obj;
		boolean equalSameOrder = this.getOneElement().equals(other.getOneElement()) 
				&& this.getOtherElement().equals(other.getOtherElement());
		if (equalSameOrder) {
			return true;
		}
		boolean equalSwapedOrder = this.getOneElement().equals(other.getOtherElement()) 
				&& this.getOtherElement().equals(other.getOneElement());
		if (equalSwapedOrder) {
			return true;
		}
		return false;
	}
	@Override
	public String toString() {
		return "[" + m_OneElement + ", " + m_OtherElement + "]";
	}
	
	

}
