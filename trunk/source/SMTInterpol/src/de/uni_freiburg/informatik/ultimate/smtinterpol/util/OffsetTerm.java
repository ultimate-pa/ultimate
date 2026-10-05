/*
 * Copyright (C) 2009-2026 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.smtinterpol.util;

import java.util.Arrays;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants;
import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 * A numeric term split syntactically into its offset-free part and a constant
 * offset: a trailing constant summand of a {@code +} application is the offset,
 * and dropping it yields the offset-free part; a term that is entirely constant
 * splits into the base {@code 0} and its value (matching the {@code 0} CCTerm
 * that a plain-numeral parameter is based on). This is the exact inverse of
 * {@code CCParameter.addConstant} and {@code TermCompiler.unifyPolynomial}, which
 * both place the constant last behind the canonic offset-free term, so equal
 * values always split into byte-identical offset-free parts. A constant summand
 * in any other position (possible only when offset equalities are disabled and
 * constants never move between equality sides) is deliberately left inside the
 * offset-free part.
 */
public class OffsetTerm {
	private final Term mTerm;
	private final Rational mOffset;

	public OffsetTerm(final Term term) {
		Term base = term;
		Rational offset = Rational.ZERO;
		if (term.getSort().isNumericSort()) {
			if (base instanceof ApplicationTerm
					&& ((ApplicationTerm) base).getFunction().getName().equals(SMTLIBConstants.PLUS)) {
				final Term[] params = ((ApplicationTerm) base).getParameters();
				final Rational last = Polynomial.parseConstant(params[params.length - 1]);
				if (last != null) {
					offset = last;
					base = params.length == 2 ? params[0]
							: term.getTheory().term(SMTLIBConstants.PLUS, Arrays.copyOf(params, params.length - 1));
				}
			} else if (base instanceof ConstantTerm) {
				// a plain constant is all offset; its offset-free part is the 0 base term
				final Rational baseConstant = Polynomial.parseConstant(base);
				if (baseConstant != null) {
					offset = offset.add(baseConstant);
					base = Rational.ZERO.toTerm(term.getSort());
				}
			}
		}
		mTerm = base;
		mOffset = offset;
	}

	public Term getTerm() {
		return mTerm;
	}

	public Rational getOffset() {
		return mOffset;
	}
}
