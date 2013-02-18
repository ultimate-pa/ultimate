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
package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.linar;

import de.uni_freiburg.informatik.ultimate.logic.Rational;

public class ExactInfinitNumber {
	private Rational m_Real;
	private Rational m_Eps;
	public ExactInfinitNumber(Rational real, Rational eps) {
		m_Real = real;
		m_Eps = eps;
	}
	public Rational getRealValue() {
		return m_Real;
	}
	public Rational getEpsilon() {
		return m_Eps;
	}
	public String toString() {
		if (m_Eps.signum() == 0)
			return m_Real.toString();
		if (m_Eps.signum() > 0)
			return m_Real.toString() + "+" + m_Eps.toString() + "eps";
		return m_Real.toString() + "-" + m_Eps.abs().toString() + "eps";
	}
	public boolean equals(Object o) {
		if (o instanceof ExactInfinitNumber) {
			ExactInfinitNumber n = (ExactInfinitNumber) o;
			return m_Real.equals(n.m_Real) && m_Eps == n.m_Eps;
		}
		return false;
	}
	public int hashCode() {
		return m_Real.hashCode() + 65537 * m_Eps.hashCode();
	}
}
