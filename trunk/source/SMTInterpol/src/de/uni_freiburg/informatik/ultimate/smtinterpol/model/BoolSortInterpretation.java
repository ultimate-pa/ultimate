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
	
	private final static int TRUE_INDEX = 1;
	private final static int FALSE_INDEX = 0;

	@Override
	public Term toSMTLIB(Theory t, Sort sort) {
		throw new InternalError("Should never be called");
	}

	public int getFalseIdx() {
		return FALSE_INDEX;
	}
	
	public int getTrueIdx() {
		return TRUE_INDEX;
	}

	@Override
	public int ensureCapacity(int maxValue) {
		if (maxValue > 2) {
			throw new InternalError("Three-valued Bool?");
		}
		return 2;
	}

	@Override
	public int size() {
		return 2;
	}

	@Override
	public Term get(int idx, Sort s, Theory t) throws IndexOutOfBoundsException {
		if (idx != TRUE_INDEX && idx != FALSE_INDEX) {
			throw new IndexOutOfBoundsException();
		}
		return idx == TRUE_INDEX ? t.mTrue : t.mFalse;
	}

	@Override
	public int extendFresh() {
		throw new InternalError("Three-valued Bool?");
	}

}
