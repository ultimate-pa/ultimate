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
package de.uni_freiburg.informatik.ultimate.smtinterpol.model;

import java.math.BigDecimal;
import java.math.BigInteger;

import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermTransformer;

/**
 * {@link ConstantTerm}s that have numeric sort (Int, Real) can represent their
 * value either as {@link BigInteger}, {@link BigDecimal}, or {@link Rational}.
 * This class helps us to establish a normal form in which values are always
 * represented by {@link Rational}s.
 *
 * @author Matthias Heizmann (matthias.heizmann@iste.uni-stuttgart.de>)
 *
 */
public class ConstantTermNormalizer extends TermTransformer {

	@Override
	protected void convert(final Term term) {
		if (term instanceof ConstantTerm) {
			final Term res;
			final ConstantTerm ct = (ConstantTerm) term;
			res = convertConstantTerm(term, ct);
			setResult(res);
		} else {
			super.convert(term);
		}
	}

	private static Term convertConstantTerm(final Term term, final ConstantTerm ct) {
		if (!ct.getSort().isNumericSort()) {
			// do nothing, only applicable to numeric sorts
			return ct;
		}
		if (ct.getValue() instanceof BigInteger) {
			final Rational rat = Rational.valueOf((BigInteger) ct.getValue(), BigInteger.ONE);
			return rat.toTerm(term.getSort());
		} else if (ct.getValue() instanceof BigDecimal) {
			final BigDecimal decimal = (BigDecimal) ct.getValue();
			Rational rat;
			if (decimal.scale() <= 0) {
				final BigInteger num = decimal.toBigInteger();
				rat = Rational.valueOf(num, BigInteger.ONE);
			} else {
				final BigInteger num = decimal.unscaledValue();
				final BigInteger denom = BigInteger.TEN.pow(decimal.scale());
				rat = Rational.valueOf(num, denom);
			}
			return rat.toTerm(term.getSort());
		} else if (ct.getValue() instanceof Rational) {
			// do nothing, already in normal form
			return ct;
		} else {
			throw new AssertionError("Value has to be either BigInteger, Decimal, or Rational");
		}
	}

}
