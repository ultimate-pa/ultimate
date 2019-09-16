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

import java.math.BigInteger;

import de.uni_freiburg.informatik.ultimate.smtinterpol.util.ArrayMap;

/**
 * Class representing a linear term c1*x1+...+cn*xn
 *
 * @author Juergen Christ
 */
public class LinTerm extends ArrayMap<LinVar, BigInteger> {
	/**
	 * Generate a new linear term. Note that we do not make a copy of the given
	 * map.
	 * @param coeffmap Coefficient map to use.
	 */
	LinTerm(LinVar[] vars, BigInteger[] coeffs) {
		super(vars, coeffs);
	}

	@Override
	public String toString() {
		if (isEmpty()) {
			return "0";
		}
		final StringBuilder sb = new StringBuilder();
		boolean isFirst = true;
		for (final Entry<LinVar, BigInteger> entry : entrySet()) {
			final LinVar var = entry.getKey();
			BigInteger fact = entry.getValue();
			if (fact.signum() == -1) {
				sb.append(isFirst ? "-" : " - ");
			} else {
				sb.append(isFirst ? "" : " + ");
			}
			fact = fact.abs();
			if (!fact.equals(BigInteger.ONE)) {
				sb.append(fact).append('*');
			}
			sb.append(var);
			isFirst = false;
		}
		return sb.toString();
	}
}
