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
package de.uni_freiburg.informatik.ultimate.smtinterpol.util;

import com.github.jhoenicke.javacup.runtime.Symbol;
import com.github.jhoenicke.javacup.runtime.SymbolFactory;

public class MySymbolFactory implements SymbolFactory {
	public class LineColumnSymbol extends Symbol {
		private final String mName;
		private final int mLColumn;
		private final int mRColumn;

		public LineColumnSymbol(final String name, final int id, final int state) {
			super(id, state);
			mName = name;
			mLColumn = -1;
			mRColumn = -1;
		}

		public LineColumnSymbol(final String name, final int id, final int left, final int lcolumn, final int right,
				final int rcolumn, final Object o) {
			super(id, left, right, o);
			mName = name;
			mLColumn = lcolumn;
			mRColumn = rcolumn;
		}

		public LineColumnSymbol(final String name, final int id, final Symbol left, final Symbol right,
				final Object o) {
			super(id, left, right, o);
			mName = name;
			if (left instanceof LineColumnSymbol) {
				mLColumn = ((LineColumnSymbol) left).mLColumn;
			} else {
				mLColumn = 0;
			}
			if (right instanceof LineColumnSymbol) {
				mRColumn = ((LineColumnSymbol) left).mRColumn;
			} else {
				mRColumn = 0;
			}
		}

		public String getLocation() {
			if (mLColumn >= 0) {
				return left + ":" + mLColumn;
			}
			return Integer.toString(left);
		}

		public String getName() {
			return mName;
		}

		@Override
		public String toString() {
			return "(" + mName + " " + left + ":" + mLColumn + "-" + right + ":" + mRColumn + ")";
		}
	}

	// Factory methods
	public Symbol newSymbol(final String name, final int id, final int lline, final int lcol, final int rline,
			final int rcol, final Object value) {
		return new LineColumnSymbol(name, id, lline, lcol, rline, rcol, value);
	}

	public Symbol newSymbol(final String name, final int id, final int lline, final int lcol, final int rline,
			final int rcol) {
		return new LineColumnSymbol(name, id, lline, lcol, rline, rcol, null);
	}

	@Override
	public Symbol newSymbol(final String name, final int id, final Symbol left, final Symbol right,
			final Object value) {
		return new LineColumnSymbol(name, id, left, right, value);
	}

	@Override
	public Symbol newSymbol(final String name, final int id, final Symbol left, final Symbol right) {
		return new LineColumnSymbol(name, id, left, right, null);
	}

	@Override
	public Symbol newSymbol(final String name, final int id) {
		return new LineColumnSymbol(name, id, -1, -1, -1, -1, null);
	}

	@Override
	public Symbol newSymbol(final String name, final int id, final Object value) {
		return new LineColumnSymbol(name, id, -1, -1, -1, -1, value);
	}

	@Override
	public Symbol startSymbol(final String name, final int id, final int state) {
		final LineColumnSymbol s = new LineColumnSymbol(name, id, state);
		return s;
	}
}
