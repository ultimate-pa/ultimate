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
package de.uni_freiburg.informatik.ultimate.logic;

import java.util.Iterator;
import java.util.Map;
import java.util.NoSuchElementException;

/**
 * Class used as a response to get-assignments.  This class carries truth values
 * for all named Boolean terms that are asserted so far.
 * @author Juergen Christ
 */
public class Assignments {
	/**
	 * Iterator over all assignments with one specific Boolean value.  This is
	 * essentially a filtering iterator.
	 * @author Juergen Christ
	 */
	private class TruthIterator implements Iterator<String> {
		/**
		 * The value we want to filter.
		 */
		private final Boolean mTruthVal;
		/**
		 * The filtered iterator.
		 */
		private final Iterator<Map.Entry<String, Boolean>> mIt;
		/**
		 * The next value to return.
		 */
		private String mNextVal;
		/**
		 * Initialize the filter iterator.
		 * @param truthVal
		 */
		public TruthIterator(Boolean truthVal) {
			mTruthVal = truthVal;
			mIt = mAssignment.entrySet().iterator();
			nextVal();
		}
		/**
		 * Search for the next value to return.
		 */
		private void nextVal() {			
			while (mIt.hasNext()) {
				final Map.Entry<String, Boolean> me = mIt.next();
				if (me.getValue() == mTruthVal) {
					mNextVal = me.getKey();
					return;
				}
			}
			mNextVal = null;
		}
		
		@Override
		public boolean hasNext() {
			return mNextVal != null;
		}

		@Override
		public String next() {
			final String val = mNextVal;
			if (val == null) {
				throw new NoSuchElementException();
			}
			nextVal();
			return val;
		}

		@Override
		public void remove() {
			throw new UnsupportedOperationException();
		}
		
	}
	/**
	 * Store the assignment.
	 */
	private final Map<String, Boolean> mAssignment;
	/**
	 * The number of labels assigned to true.  This is lazily computed.
	 */
	private int mNumTrue = -1;
	/**
	 * Construct a new assignment.
	 * @param assignment Map containing the assignments extracted by the solver.
	 */
	public Assignments(Map<String, Boolean> assignment) {
		mAssignment = assignment;
	}
	/**
	 * Get the assignment of a named Boolean term.
	 * @param label Label of the Boolean term.
	 * @return Truth value assigned to the corresponding named Boolean term.
	 */
	public Boolean getAssignment(String label) {
		return mAssignment.get(label);
	}
	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();
		sb.append('(');
		for (final Map.Entry<String, Boolean> me : mAssignment.entrySet()) {
			sb.append('(').append(me.getKey()).append(' ').
				append(me.getValue()).append(')');
		}
		sb.append(')');
		return sb.toString();
	}
	/**
	 * Iterate over all labels whose corresponding named Boolean term is
	 * assigned <code>true</code> in the current model.
	 * @return Iterator over all satisfied named Boolean terms.
	 */
	public Iterable<String> getTrueAssignments() {
		return new Iterable<String>() {
			
			@Override
			public Iterator<String> iterator() {
				return new TruthIterator(Boolean.TRUE);
			}
		};
	}
	/**
	 * Iterate over all labels whose corresponding named Boolean term is
	 * assigned <code>false</code> in the current model.
	 * @return Iterator over all falsified named Boolean terms.
	 */
	public Iterable<String> getFalseAssignments() {
		return new Iterable<String>() {
			
			@Override
			public Iterator<String> iterator() {
				return new TruthIterator(Boolean.FALSE);
			}
		};
	}
	/**
	 * Get the number of labels assigned to true.
	 * @return Number of labels assigned to true.
	 */
	public int getNumTrueAssignments() {
		if (mNumTrue == -1) {
			mNumTrue = 0;
			for (final Map.Entry<String, Boolean> me : mAssignment.entrySet()) {
				if (me.getValue() == Boolean.TRUE) {
					++mNumTrue;
				}
			}
		}
		return mNumTrue;
	}
	/**
	 * Get the number of labels assigned to false.
	 * @return Number of labels assigned to false.
	 */
	public int getNumFalseAssignments() {
		return mAssignment.size() - getNumTrueAssignments();
	}
}
