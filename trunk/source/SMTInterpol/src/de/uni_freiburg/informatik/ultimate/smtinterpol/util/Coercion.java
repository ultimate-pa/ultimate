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
package de.uni_freiburg.informatik.ultimate.smtinterpol.util;

import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.SMTAffineTerm;

/**
 * Helper class to factor out coercions needed in IRA-Logics
 * @author Juergen Christ
 */
public final class Coercion {

	private Coercion() {
		// Hide constructor
	}
	public static Term toReal(final Term t) {
		assert t.getSort().getName().equals("Int");
		if (t instanceof ConstantTerm) {
			final Rational val = SMTAffineTerm.convertConstant((ConstantTerm) t).floor();
			assert val.isIntegral();
			return val.toTerm(t.getTheory().getSort("Real"));
		}
		return t.getTheory().term("to_real", t);
	}
	public static Term coerce(final Term t, final Sort s) {
		if (t.getSort() == s) {
			return t;
		}
		if (s.getName().equals("Real")) {
			return toReal(t);
		}
		throw new InternalError("Should only be called with numeric sort!");
	}
	/// BE CAREFUL: args might be modified!!!
	public static Term buildApp(final FunctionSymbol fsymb, final Term[] args) {
		final Sort[] paramSorts = fsymb.getParameterSorts();
		if (fsymb.getTheory().getLogic().isIRA()) {
			for (int i = 0; i < args.length; ++i) {
				if (args[i].getSort() != paramSorts[i]) {
					args[i] = coerce(args[i], paramSorts[i]);
				}
			}
		}
		return fsymb.getTheory().term(fsymb, args);
	}

	public static Term buildEq(Term lhs, Term rhs) {
		if (lhs.getSort() != rhs.getSort()) {
			assert lhs.getTheory().getLogic().isIRA();
			if (!lhs.getSort().getName().equals("Real")) {
				lhs = toReal(lhs);
			}
			if (!rhs.getSort().getName().equals("Real")) {
				rhs = toReal(rhs);
			}
		}
		return lhs.getTheory().term("=", lhs, rhs);
	}

	public static Term buildDistinct(Term lhs, Term rhs) {
		if (lhs.getSort() != rhs.getSort()) {
			assert lhs.getTheory().getLogic().isIRA();
			if (!lhs.getSort().getName().equals("Real")) {
				lhs = toReal(lhs);
			}
			if (!rhs.getSort().getName().equals("Real")) {
				rhs = toReal(rhs);
			}
		}
		return lhs.getTheory().distinct(lhs, rhs);
	}
}
