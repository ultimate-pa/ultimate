/*
 *
 * This file is part of the PEA tool set
 *
 * The PEA tool set is a collection of tools for
 * Phase Event Automata (PEA). See
 * http://csd.informatik.uni-oldenburg.de/projects/peatools.html
 * for more information.
 *
 * Copyright (C) 2005-2006, Department for Computing Science,
 *                          University of Oldenburg
 *
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License
 * as published by the Free Software Foundation; either version 2
 * of the License, or (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301, USA
 */
package de.uni_freiburg.informatik.ultimate.lib.pea;

import java.util.Arrays;
import java.util.Collections;
import java.util.Iterator;
import java.util.Set;
import java.util.stream.Collectors;

import net.sourceforge.czt.z.util.ZString;

/**
 * Represents a counter example trace. A counter example trace is a sequence of phases (represented by
 * CounterTrace.DCPhase). Each phase has an invariant, a set of forbidden events, a set of entry events and an optional
 * upper or lower bound.
 */
public class CounterTrace {

	public enum BoundTypes {
		LESS(-2), LESSEQUAL(-1), NONE(0), GREATEREQUAL(1), GREATER(2);

		private int mVal;

		private BoundTypes(final int i) {
			mVal = i;
		}

		public int asValue() {
			return mVal;
		}
	}

	public static final int BOUND_LESS = -2;
	public static final int BOUND_LESSEQUAL = -1;
	public static final int BOUND_NONE = 0;
	public static final int BOUND_GREATEREQUAL = 1;
	public static final int BOUND_GREATER = 2;

	private final DCPhase[] mPhases;

	public CounterTrace(final DCPhase[] phases) {
		mPhases = phases;
	}

	public DCPhase[] getPhases() {
		return mPhases;
	}

	/***
	 * Returns the successor phase of a phase in a counter trace. Returns null if phase is already the last phase.
	 *
	 * @param phase
	 * @return successor of phase, or null if phase is last phase
	 */
	public DCPhase getSuccessor(final DCPhase phase) {
		for (int i = 0; i < getPhases().length; i++) {
			if (getPhases()[i] == phase && i < getPhases().length - 1) {
				return getPhases()[i + 1];
			}
		}
		return null;
	}

	@Override
	public String toString() {
		return Arrays.stream(getPhases()).map(a -> a.toString(true)).collect(Collectors.joining(";"));
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + Arrays.hashCode(mPhases);
		return result;
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		}
		if (obj == null || getClass() != obj.getClass()) {
			return false;
		}
		final CounterTrace other = (CounterTrace) obj;
		return Arrays.equals(mPhases, other.mPhases);
	}

	public static class DCPhase {

		private final CDD mEntryEvents;
		private final CDD mInvariant;
		private final int mBoundType;
		private final int mBound;
		private final Set<String> mForbid;
		private final boolean mAllowEmpty;

		public DCPhase(final CDD ee, final CDD i, final int bt, final int b, final Set<String> f, final boolean empty) {
			mEntryEvents = ee;
			mInvariant = i;
			mBound = b;
			/*
			 * the current implementation of Trace2PEACompiler requires (for non-empty phases) that \ell > 0 and \ell
			 * \geq 0 are modelled with boundType = BOUND_NONE
			 */
			mBoundType = (!empty && b == 0 && bt > 0 ? BOUND_NONE : bt);
			mForbid = f;
			mAllowEmpty = empty;
		}

		public DCPhase(final CDD ee, final CDD i, final int bt, final int b, final Set<String> f) {
			this(ee, i, bt, b, f, false);
		}

		public DCPhase(final CDD i, final int bt, final int b, final Set<String> f) {
			this(CDD.TRUE, i, bt, b, f, false);
		}

		public DCPhase(final CDD ee, final CDD i, final Set<String> f) {
			this(ee, i, BOUND_NONE, 0, f, false);
		}

		public DCPhase(final CDD i, final Set<String> f) {
			this(CDD.TRUE, i, BOUND_NONE, 0, f, false);
		}

		public DCPhase(final CDD ee, final CDD i, final int bt, final int b) {
			this(ee, i, bt, b, Collections.emptySet(), false);
		}

		public DCPhase(final CDD i, final int bt, final int b) {
			this(CDD.TRUE, i, bt, b, Collections.emptySet(), false);
		}

		public DCPhase(final CDD ee, final CDD i) {
			this(ee, i, BOUND_NONE, 0, Collections.emptySet(), false);
		}

		public DCPhase(final CDD i) {
			this(CDD.TRUE, i, BOUND_NONE, 0, Collections.emptySet(), false);
		}

		/**
		 * Create a ell ~ bound phase (with allowEmpty set if no lower bound).
		 */
		public DCPhase(final int bt, final int b) {
			this(CDD.TRUE, CDD.TRUE, bt, b, Collections.emptySet(), bt <= 0);
		}

		/**
		 * Create a true phase (with allowEmpty set).
		 */
		public DCPhase() {
			this(CDD.TRUE, CDD.TRUE, BOUND_NONE, 0, Collections.emptySet(), true);
		}

		/**
		 * @return Returns the allowEmpty.
		 */
		public boolean isAllowEmpty() {
			return mAllowEmpty;
		}

		public String toString(final boolean useUnicode) {
			final String AND = useUnicode ? ZString.AND : "/\\";
			final String NOEVENT = useUnicode ? "\u229F" : "[-]";
			final String EMPTY = useUnicode ? "\u2080" : "0";
			final String GEQ = useUnicode ? ZString.GEQ : ">=";
			final String LEQ = useUnicode ? ZString.LEQ : "<=";

			final String LCEIL = useUnicode ? "\u2308" : "[";
			final String RCEIL = useUnicode ? "\u2309" : "]";
			final String ELL = useUnicode ? "\u2113" : "L";

			final StringBuilder sb = new StringBuilder();
			if (getEntryEvents() != CDD.TRUE) {
				sb.append(getEntryEvents()).append(" ; ");
			}

			if (getInvariant() == CDD.TRUE && isAllowEmpty()) {
				sb.append(getInvariant());
			} else {
				sb.append(LCEIL).append(getInvariant()).append(RCEIL);
			}

			for (final Iterator<?> it = mForbid.iterator(); it.hasNext();) {
				sb.append(' ').append(AND).append(' ').append(NOEVENT).append(' ').append(it.next());
			}

			if (getBoundType() != BOUND_NONE) {
				sb.append(' ').append(AND).append(' ').append(ELL);
				switch (getBoundType()) {
				case BOUND_LESS:
					if (!isAllowEmpty()) {
						sb.append(" < ");
						break;
					}
					sb.append(" <").append(EMPTY).append(' ');
					break;
				case BOUND_LESSEQUAL:
					if (!isAllowEmpty()) {
						sb.append(' ').append(LEQ).append(' ');
						break;
					}
					sb.append(' ').append(LEQ).append(EMPTY).append(' ');
					break;
				case BOUND_GREATER:
					if (!isAllowEmpty()) {
						sb.append(" > ");
						break;
					}
					sb.append(" >").append(EMPTY).append(' ');
					break;
				case BOUND_GREATEREQUAL:
					if (!isAllowEmpty()) {
						sb.append(' ').append(GEQ).append(' ');
						break;
					}
					sb.append(' ').append(GEQ).append(EMPTY).append(' ');
					break;
				default:
					throw new IllegalArgumentException();
				}
				sb.append(getBound());
			}

			return sb.toString();
		}

		@Override
		public String toString() {
			return toString(true);
		}

		/**
		 * @return Returns the boundType.
		 */
		public int getBoundType() {
			return mBoundType;
		}

		/**
		 * @return Returns the forbid.
		 */
		public Set<String> getForbid() {
			return mForbid;
		}

		/**
		 * @return Returns the invariant.
		 */
		public CDD getInvariant() {
			return mInvariant;
		}

		public CDD getEntryEvents() {
			return mEntryEvents;
		}

		public int getBound() {
			return mBound;
		}

		@Override
		public int hashCode() {
			final int prime = 31;
			int result = 1;
			result = prime * result + (mAllowEmpty ? 1231 : 1237);
			result = prime * result + mBound;
			result = prime * result + mBoundType;
			result = prime * result + ((mEntryEvents == null) ? 0 : mEntryEvents.hashCode());
			result = prime * result + ((mForbid == null) ? 0 : mForbid.hashCode());
			result = prime * result + ((mInvariant == null) ? 0 : mInvariant.hashCode());
			return result;
		}

		@Override
		public boolean equals(final Object obj) {
			if (this == obj) {
				return true;
			}
			if (obj == null || getClass() != obj.getClass()) {
				return false;
			}
			final DCPhase other = (DCPhase) obj;
			if (mAllowEmpty != other.mAllowEmpty) {
				return false;
			}
			if (mBound != other.mBound) {
				return false;
			}
			if (mBoundType != other.mBoundType) {
				return false;
			}
			if (mEntryEvents == null) {
				if (other.mEntryEvents != null) {
					return false;
				}
			} else if (!mEntryEvents.equals(other.mEntryEvents)) {
				return false;
			}
			if (mForbid == null) {
				if (other.mForbid != null) {
					return false;
				}
			} else if (!mForbid.equals(other.mForbid)) {
				return false;
			}
			if (mInvariant == null) {
				if (other.mInvariant != null) {
					return false;
				}
			} else if (!mInvariant.equals(other.mInvariant)) {
				return false;
			}
			return true;
		}

	}

}
