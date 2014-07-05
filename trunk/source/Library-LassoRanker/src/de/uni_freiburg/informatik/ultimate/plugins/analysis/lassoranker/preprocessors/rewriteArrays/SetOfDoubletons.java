package de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.preprocessors.rewriteArrays;

import java.util.ArrayList;
import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.util.HashRelation;

/**
 * Objects of this class represent a set of Doubletons. (We call a multiset
 * of two elements a Doubleton)
 * @author Matthias Heizmann
 *
 */
public class SetOfDoubletons<E> {
	
	private final HashRelation<E, E> m_SomeElem2OtherElem;
	private final List<Doubleton<E>> m_Elements;
	public SetOfDoubletons() {
		super();
		m_SomeElem2OtherElem = new HashRelation<>();
		m_Elements = new ArrayList<Doubleton<E>>();
	}
	
	public boolean containsDoubleton(Doubleton<E> twoelton) {
		return containsDoubleton(twoelton.getOneElement(), twoelton.getOtherElement());
	}
	
	public boolean containsDoubleton(E oneElem, E otherElem) {
		Set<E> image = m_SomeElem2OtherElem.getImage(oneElem);
		if (image == null) {
			return false;
		} else {
			return image.contains(otherElem);
		}
	}
	
	
	public void addDoubleton(Doubleton<E> doubleton) {
		if (!containsDoubleton(doubleton)) {
			m_SomeElem2OtherElem.addPair(doubleton.getOneElement(), doubleton.getOtherElement());
			m_SomeElem2OtherElem.addPair(doubleton.getOtherElement(), doubleton.getOneElement());
			m_Elements.add(doubleton);
		}
	}
	
//	public Set<E> getSecondElements(E elem) {
//		return m_Elem2Twoelton.getImage(elem);
//	}
	
	public Iterable<Doubleton<E>> elements() {
		return m_Elements;
	}
	
	@Override
	public String toString() {
		return m_Elements.toString();
	}
	

}
