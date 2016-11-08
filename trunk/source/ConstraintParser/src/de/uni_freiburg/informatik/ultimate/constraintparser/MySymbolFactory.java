/*
 * Copyright (C) 2012-2015 Sergiy Bogomolov
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE ConstraintParser plug-in.
 * 
 * The ULTIMATE ConstraintParser plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE ConstraintParser plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ConstraintParser plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ConstraintParser plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE ConstraintParser plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.constraintparser;

import com.github.jhoenicke.javacup.runtime.Symbol;
import com.github.jhoenicke.javacup.runtime.SymbolFactory;

public class MySymbolFactory implements SymbolFactory {
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
		return new LineColumnSymbol(name, id, state);
	}
	
	class LineColumnSymbol extends Symbol {
		private final String mName;
		private final int mLcolumn;
		private final int mRcolumn;
		
		public LineColumnSymbol(final String name, final int id, final int state) {
			// Grrr, the constructor is protected, but
			// at least the field is writeable...
			super(id);
			parse_state = state;
			mName = name;
			mLcolumn = -1;
			mRcolumn = -1;
		}
		
		public LineColumnSymbol(final String name, final int id,
				final int left, final int lcolumn, final int right, final int rcolumn,
				final Object o) {
			super(id, left, right, o);
			mName = name;
			mLcolumn = lcolumn;
			mRcolumn = rcolumn;
		}
		
		public LineColumnSymbol(final String name, final int id, final Symbol left, final Symbol right,
				final Object o) {
			super(id, left, right, o);
			mName = name;
			if (left instanceof LineColumnSymbol) {
				mLcolumn = ((LineColumnSymbol) left).mLcolumn;
			} else {
				mLcolumn = 0;
			}
			if (right instanceof LineColumnSymbol) {
				mRcolumn = ((LineColumnSymbol) left).mRcolumn;
			} else {
				mRcolumn = 0;
			}
		}
		
		public String getLocation() {
			if (mLcolumn >= 0) {
				return left + ":" + mLcolumn;
			}
			return Integer.toString(left);
		}
		
		public String getName() {
			return mName;
		}
		
		@Override
		public String toString() {
			return "(" + mName + " " + left + ":" + mLcolumn + "-" + right + ":" + mRcolumn + ")";
		}
	}
}
