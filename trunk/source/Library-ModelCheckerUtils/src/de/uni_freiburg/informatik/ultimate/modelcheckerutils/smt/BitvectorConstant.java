/*
 * Copyright (C) 2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE ModelCheckerUtils Library.
 * 
 * The ULTIMATE ModelCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE ModelCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ModelCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ModelCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE ModelCheckerUtils Library grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt;

import java.math.BigInteger;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 * 
 * @author Matthias Heizmann
 *
 */
public class BitvectorConstant {
	private final BigInteger m_Value;
	private final BigInteger m_Index;
	private final Term m_Term;
	
	public BitvectorConstant(Term term) {
		if (term instanceof ApplicationTerm) {
			if (term.getSort().getName().equals("BitVec")) {
				if (term.getSort().getIndices().length == 1) {
					ApplicationTerm appTerm = (ApplicationTerm) term;
					if (appTerm.getParameters().length == 0) {
						String funName = appTerm.getFunction().getName();
						if (funName.startsWith("bv")) {
							String value = funName.substring(2);
							m_Value = new BigInteger(value);
							m_Index = term.getSort().getIndices()[0];
							m_Term = term;
							return;
						}
					}
				}
			}
		}
		m_Value = null;
		m_Index = null;
		m_Term = null;
	}
	
	boolean isBitvectorConstant() {
		return m_Value != null && m_Index != null;
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((m_Index == null) ? 0 : m_Index.hashCode());
		result = prime * result + ((m_Value == null) ? 0 : m_Value.hashCode());
		return result;
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj == null)
			return false;
		if (getClass() != obj.getClass())
			return false;
		BitvectorConstant other = (BitvectorConstant) obj;
		if (m_Index == null) {
			if (other.m_Index != null)
				return false;
		} else if (!m_Index.equals(other.m_Index))
			return false;
		if (m_Value == null) {
			if (other.m_Value != null)
				return false;
		} else if (!m_Value.equals(other.m_Value))
			return false;
		return true;
	}

	@Override
	public String toString() {
		return String.valueOf(m_Term);
	}
	

	
	
}
