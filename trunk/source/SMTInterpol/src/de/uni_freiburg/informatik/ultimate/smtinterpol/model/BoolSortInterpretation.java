/*
 * Copyright (C) 2014 University of Freiburg
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

import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Theory;

public class BoolSortInterpretation implements SortInterpretation {

	@Override
	public Term toSMTLIB(final Theory t, final Sort sort) {
		throw new AssertionError("Should never be called");
	}

	@Override
	public Term extendFresh(final Sort sort) {
		throw new AssertionError("Three-valued Bool?");
	}

	@Override
	public Term getModelValue(final int idx, final Sort sort) {
		return idx == 0 ? sort.getTheory().mFalse : sort.getTheory().mTrue;
	}

	@Override
	public void register(Term term) {
		assert term == term.getTheory().mFalse || term == term.getTheory().mTrue;
	}
}
