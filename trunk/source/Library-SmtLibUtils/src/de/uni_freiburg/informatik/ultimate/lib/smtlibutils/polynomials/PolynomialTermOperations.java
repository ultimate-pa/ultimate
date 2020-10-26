/*
 * Copyright (C) 2020 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2020 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials;

import de.uni_freiburg.informatik.ultimate.logic.Rational;

/**
 * Provides static methods for combining {@link IPolynomialTerm}s. Methods make sure that {@link AffineTerm}s are
 * returned if {@link PolynomialTerm}s are not needed.
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 */
public class PolynomialTermOperations {

	private PolynomialTermOperations() {
		// do not instantiate
	}

	public static IPolynomialTerm mul(final IPolynomialTerm poly, final Rational rat) {
		if (poly instanceof AffineTerm) {
			return AffineTerm.mul(poly, rat);
		} else if (poly instanceof PolynomialTerm) {
			return PolynomialTerm.mul(poly, rat);
		} else {
			throw new AssertionError("unknown kind of IPolynomialTerm");
		}
	}

	public static IPolynomialTerm sum(final IPolynomialTerm mul, final AffineTerm affineTerm) {
		throw new UnsupportedOperationException();
	}

}
