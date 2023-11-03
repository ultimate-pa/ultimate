/*
 * Copyright (C) 2019 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.quant;

import de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants;
import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 * A quantified equality atom of the form "Term = Term".
 *
 * If the equality contains a variable at top level, it is of the form "TermVariable = Term"
 *
 * @author Tanja Schindler
 *
 */
public class QuantEquality extends QuantLiteral {

	private final Term mLhs, mRhs;

	public QuantEquality(final Term lhs, final Term rhs) {
		super(lhs.getTheory().term(SMTLIBConstants.EQUALS, lhs, rhs));
		mLhs = lhs;
		mRhs = rhs;
		mNegated = new NegQuantLiteral(this);
	}

	public Term getLhs() {
		return mLhs;
	}

	public Term getRhs() {
		return mRhs;
	}
}
