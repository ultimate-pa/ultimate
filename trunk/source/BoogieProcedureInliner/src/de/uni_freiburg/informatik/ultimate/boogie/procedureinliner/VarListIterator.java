package de.uni_freiburg.informatik.ultimate.boogie.procedureinliner;

import java.util.NoSuchElementException;

import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VarList;

/**
 * Iterates over multiple groups of VarLists at the same time.
 * All groups must have the same number of variables, but the partitioning of the groups into VarLists can differ.
 *
 * This is no java.util.Iterator, because next() would have to return a tuple of elements,
 * which would be unnecessary overhead. You can use this class to access the elements of the tuple instead.
 *
 * @author schaetzc@informatik.uni-freiburg.de
 */
public class VarListIterator {
	
	/** Number of VarList groups. */
	private int mGroups;
	
	/** Number of variables per group. This is the "length" of the iterator. */
	private int mVars;
	
	/** Current position of the iterator. */
	private int mCursor;
	
	/** Groups of VarLists. Use mVarListGroups[group][listFromTheGroup]. All groups contain {@link #mVars} variables. */
	private VarList[][] mVarListGroups;
	
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
			for (VarList vl : mVarListGroups[group]) {
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
			int[] groupVarListIndices = new int[mVars];
			int[] groupIdIndices = new int[mVars]; 
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
	
	public void next() {
		if (hasNext()) {
			++mCursor;
		} else {
			throw new NoSuchElementException();
		}
	}

	public String currentId(int group) {
		return currentVarList(group).getIdentifiers()[mIdIndices[group][mCursor]];
	}

	public VarList currentVarList(int group) {
		return mVarListGroups[group][mVarListIndices[group][mCursor]];
	}
	
	public boolean varListChanged(int group) {
		if (mCursor > 0) {
			int[] varListIndicies = mVarListIndices[group];
			return varListIndicies[mCursor - 1] != varListIndicies[mCursor];
		} else {
			return true;
		}
	}
}
