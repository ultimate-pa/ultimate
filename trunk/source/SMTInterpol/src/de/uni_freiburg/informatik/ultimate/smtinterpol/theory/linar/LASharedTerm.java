/*
 * Copyright (C) 2009-2020 University of Freiburg
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

import java.util.Map;

import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Term;

public class LASharedTerm {
	private final Map<LinVar, Rational> mSummands;
	private final Rational mOffset;
	private final Term mSMTTerm;

	public LASharedTerm(final Term term, final Map<LinVar, Rational> summands, final Rational offset) {
		mSummands = summands;
		mSMTTerm = term;
		mOffset = offset;
	}

	public Map<LinVar, Rational> getSummands() {
		return mSummands;
	}

	public Rational getOffset() {
		return mOffset;
	}

	public Term getTerm() {
		return mSMTTerm;
	}

	@Override
	public String toString() {
		return mSMTTerm.toString();
	}
}
