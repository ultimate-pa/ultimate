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

/**
 * We call a multiset of two elements a doubleton.
 * @author Matthias Heizmann
 *
 * @param <E>
 */
public class Doubleton<E> {
	
	
	private final E m_OneElement;
	private final E m_OtherElement;
	public Doubleton(E oneElement, E otherElement) {
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
		Doubleton<E> other = (Doubleton<E>) obj;
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
