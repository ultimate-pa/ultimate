/*
 * Copyright (C) 2015 Claus Schaetzle (schaetzc@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE BoogieProcedureInliner plug-in.
 * 
 * The ULTIMATE BoogieProcedureInliner plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE BoogieProcedureInliner plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE BoogieProcedureInliner plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE BoogieProcedureInliner plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE BoogieProcedureInliner plug-in grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.boogie.procedureinliner;

import java.util.NoSuchElementException;

import de.uni_freiburg.informatik.ultimate.boogie.ast.VarList;

/**
 * Iterates over multiple groups of VarLists at the same time.
 * All groups must have the same number of variables, but the partitioning of the groups into VarLists can differ.
 *
 * This is no java.util.Iterator, because next() would have to return a tuple of elements, which would be unnecessary
 * overhead. Instead, you can use this class to access the elements of the current tuple, after calling next().
 *
 * @author schaetzc@informatik.uni-freiburg.de
 */
public class VarListIterator {
	
	/** Number of VarList groups. */
	private final int mGroups;
	
	/** Number of variables per group. This is the "length" of the iterator. */
	private int mVars;
	
	/** Current position of the iterator. */
	private int mCursor = -1;
	
	/** Groups of VarLists. Use mVarListGroups[group][listFromTheGroup]. All groups contain {@link #mVars} variables. */
	private final VarList[][] mVarListGroups;
	
	/**
	 * mVarListIndices[group][var] contains the index of the VarList inside "group"-th group
	 * that contains the "var"-th variable of the group.
	 */
	private int[][] mVarListIndices;
	
	/** Similar to {@link #mVarListIndices}, but for identifiers. */
	private int[][] mIdIndices;
	
	/**
	 * Creates a new Iterator.
	 * @param varListGroups Groups of VarLists. All groups must have the same total number of variables.
	 */
	public VarListIterator(VarList[]... varListGroups) {
		mGroups = varListGroups.length;
		mVarListGroups = varListGroups;
		initLength();
		initIndices();
	}
	
	private void initLength() {
		int prevGroupVars = 0;
		for (int group = 0; group < mGroups; ++group) {
			int groupVars = 0;
			for (final VarList vl : mVarListGroups[group]) {
				groupVars += vl.getIdentifiers().length;
			}
			if (group > 0 && groupVars != prevGroupVars) {
				throw new IllegalArgumentException("VarList groups differed in number of variables.");
			}
			prevGroupVars = groupVars;
		}
		mVars = prevGroupVars;
	}
	
	private void initIndices() {
		mVarListIndices = new int[mGroups][];
		mIdIndices = new int[mGroups][];
		for (int group = 0; group < mGroups; ++group) {
			final int[] groupVarListIndices = new int[mVars];
			final int[] groupIdIndices = new int[mVars]; 
			int varListIndex = 0;
			int idIndex = 0;
			for (int var = 0; var < mVars; ++var) {
				while (idIndex >= mVarListGroups[group][varListIndex].getIdentifiers().length) {
					idIndex = 0;
					++varListIndex;
				}
				groupIdIndices[var] = idIndex;
				groupVarListIndices[var] = varListIndex;
				++idIndex;
			}
			mVarListIndices[group] = groupVarListIndices;
			mIdIndices[group] = groupIdIndices;
		}
	}

	public boolean hasNext() {
		return mCursor + 1 < mVars;
	}
	
	/**
	 * Advance to the next element(s) of this iterator.
	 * Don't call this 
	 */
	public void next() {
		if (hasNext()) {
			++mCursor;
		} else {
			throw new NoSuchElementException();
		}
	}

	public String currentId(int group) {
		checkCursorBounds();
		return currentVarList(group).getIdentifiers()[mIdIndices[group][mCursor]];
	}

	public VarList currentVarList(int group) {
		checkCursorBounds();
		return mVarListGroups[group][mVarListIndices[group][mCursor]];
	}
	
	private void checkCursorBounds() {
		if (mCursor < 0) {
			throw new IndexOutOfBoundsException("Need at least one call of next() to access any elements.");
		}
		// no need to check "mCursor > mVars" (see hasNext()) 
	}
	
	public boolean varListChanged(int group) {
		if (mCursor > 0) {
			final int[] varListIndicies = mVarListIndices[group];
			return varListIndicies[mCursor - 1] != varListIndicies[mCursor];
		} else {
			return true;
		}
	}
}
