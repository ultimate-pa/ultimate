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
package de.uni_freiburg.informatik.ultimate.logic;

import java.math.BigDecimal;
import java.util.ArrayDeque;
import java.util.Map;

public class ConstantTerm extends Term {
	/**
	 * The value of this term.  For numeral terms this is a BigInteger,
	 * for decimal terms a BigDecimal and for string terms this is a QuotedObject.
	 */
	private Object m_Value;
	private Sort m_Sort;
	
	ConstantTerm(Object value, Sort sort, int hash) {
		super(hash);
		this.m_Value = value;
		this.m_Sort = sort;
	}
	
	public Object getValue() {
		return m_Value;
	}

	public Sort getSort() {
		return m_Sort;
	}
	
	//@Override
	public void countTerms(Map<Term,Integer> map) {
		if (!map.containsKey(this)) {
			map.put(this, 1);
		} else {
			map.put(this, map.get(this) + 1);
		}
	}
	
	public String toString() {
		if (m_Value instanceof BigDecimal) {
			BigDecimal decimal = (BigDecimal)m_Value; 
			String str = decimal.toPlainString();
//			if (decimal.scale() <= 0)
//				str += ".0";
			return str;
		}
		if (m_Value instanceof Rational)
			return getTheory().rational((Rational) m_Value, getSort()).
				toStringDirect();
		return m_Value.toString();
	}
	
	public String toStringDirect() {
		return toString();
	}

	public static final int hashConstant(Object value, Sort sort) {
		return value.hashCode() ^ sort.hashCode();
	}

	@Override
	public void toStringHelper(ArrayDeque<Object> m_Todo) {
		m_Todo.add(toString());
	}
}
