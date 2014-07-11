/*
 * Copyright (C) 2012-2014 University of Freiburg
 *
 * This file is part of the ULTIMATE LassoRanker Library.
 *
 * The ULTIMATE LassoRanker Library is free software: you can redistribute it
 * and/or modify it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation, either version 3 of the
 * License, or (at your option) any later version.
 *
 * The ULTIMATE LassoRanker Library is distributed in the hope that it will
 * be useful, but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE LassoRanker Library. If not,
 * see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE LassoRanker Library, or any covered work, by
 * linking or combining it with Eclipse RCP (or a modified version of
 * Eclipse RCP), containing parts covered by the terms of the Eclipse Public
 * License, the licensors of the ULTIMATE LassoRanker Library grant you
 * additional permission to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.preprocessors.rewriteArrays;

import java.util.ArrayList;
import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.util.HashRelation;


/**
 * Objects of this class represent a set of Doubletons. (We call a multiset
 * of two elements a Doubleton.)
 * 
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
