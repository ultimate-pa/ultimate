package de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.preprocessors.rewriteArrays;

import java.util.ArrayList;
import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.util.HashRelation;

/**
 * We call a multiset of two elements a twoelton, objects of this class 
 * represent a set of twoeltons.
 * @author Matthias Heizmann
 *
 */
public class SetOfTwoeltons<E> {
	
	private final HashRelation<E, E> m_SomeElem2OtherElem;
	private final List<Twoelton<E>> m_Elements;
	public SetOfTwoeltons() {
		super();
		m_SomeElem2OtherElem = new HashRelation<>();
		m_Elements = new ArrayList<Twoelton<E>>();
	}
	
	public boolean containsTwoelton(Twoelton<E> twoelton) {
		return containsTwoelton(twoelton.getOneElement(), twoelton.getOtherElement());
	}
	
	public boolean containsTwoelton(E oneElem, E otherElem) {
		Set<E> image = m_SomeElem2OtherElem.getImage(oneElem);
		if (image == null) {
			return false;
		} else {
			return image.contains(otherElem);
		}
	}
	
	
	public void addTowelton(Twoelton<E> twoelton) {
		if (!containsTwoelton(twoelton)) {
			m_SomeElem2OtherElem.addPair(twoelton.getOneElement(), twoelton.getOtherElement());
			m_SomeElem2OtherElem.addPair(twoelton.getOtherElement(), twoelton.getOneElement());
			m_Elements.add(twoelton);
		}
	}
	
//	public Set<E> getSecondElements(E elem) {
//		return m_Elem2Twoelton.getImage(elem);
//	}
	
	public Iterable<Twoelton<E>> elements() {
		return m_Elements;
	}
	
	@Override
	public String toString() {
		return m_Elements.toString();
	}
	

}
