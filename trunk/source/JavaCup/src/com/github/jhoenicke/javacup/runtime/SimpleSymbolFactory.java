/*
 * Copyright (C) 2019 Daniel Dietsch
 * Copyright (C) 2019 University of Freiburg
 */
package com.github.jhoenicke.javacup.runtime;

/**
 *
 * Default implementation of {@link SymbolFactory} used throughout the Ultimate project
 * (https://github.com/ultimate-pa/ultimate).
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class SimpleSymbolFactory implements SymbolFactory {

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

	public static final class LineColumnSymbol extends Symbol {
		private final String mName;
		private final int mLcolumn;
		private final int mRcolumn;

		public LineColumnSymbol(final String name, final int id, final int state) {
			super(id);
			parse_state = state;
			mName = name;
			mLcolumn = -1;
			mRcolumn = -1;
		}

		public LineColumnSymbol(final String name, final int id, final int left, final int lcolumn, final int right,
				final int rcolumn, final Object o) {
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
