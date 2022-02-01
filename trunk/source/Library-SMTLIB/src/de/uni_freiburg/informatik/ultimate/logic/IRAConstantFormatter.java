/*
 * Copyright (C) 2013 University of Freiburg
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
import java.math.BigInteger;

public class IRAConstantFormatter extends TermTransformer {

	@Override
	protected void convert(Term term) {
		if (term instanceof ConstantTerm) {
			final ConstantTerm ct = (ConstantTerm) term;
			Rational rat = null;
			if (ct.getValue() instanceof Rational) {
				rat = (Rational) ct.getValue();
			} else if (ct.getValue() instanceof BigDecimal) {
				final BigDecimal val = (BigDecimal) ct.getValue();
				final int scale = val.scale();
				final BigInteger unscaled = val.unscaledValue();
				final BigInteger scaler = BigInteger.TEN.pow(scale);
				rat = Rational.valueOf(unscaled, scaler);
			} else if (ct.getValue() instanceof BigInteger) {
				rat = Rational.valueOf(
						(BigInteger) ct.getValue(), BigInteger.ONE);
			} else {
				setResult(ct);
				return;
			}
			setResult(ct.getTheory().modelRational(rat, ct.getSort()));
		} else {
			super.convert(term);
		}
	}

}
