package de.uni_freiburg.informatik.ultimate.logic;

import java.util.ArrayDeque;
import java.util.Arrays;
import java.util.BitSet;
import java.util.HashSet;
import java.util.NoSuchElementException;

/**
 * Represents an SMTLIB datatype sort.
 *
 * @author Jochen Hoenicke
 */
public class DataType extends SortSymbol {

	public static class Constructor {
		private final String mName;
		private final Sort[] mArgumentSorts;
		private final String[] mSelectors;
		private boolean mNeedsReturnOverload;

		public Constructor(final String name, final String[] selectors, final Sort[] argumentSorts) {
			mName = name;
			mSelectors = selectors;
			mArgumentSorts = argumentSorts;
		}

		public String getName() {
			return mName;
		}

		public Sort[] getArgumentSorts() {
			return mArgumentSorts;
		}

		public int getSelectorIndex(final String selector) {
			for (int i = 0; i < mSelectors.length; i++) {
				if (mSelectors[i].equals(selector)) {
					return i;
				}
			}
			throw new NoSuchElementException();
		}

		public String[] getSelectors() {
			return mSelectors;
		}

		public boolean needsReturnOverload() {
			return mNeedsReturnOverload;
		}

		@Override
		public String toString() {
			final StringBuilder sb = new StringBuilder();
			sb.append("(");
			sb.append(mName);
			if (mSelectors.length != 0) {
				for (int i = 0; i < mSelectors.length; i++) {
					sb.append(" ");
					sb.append("(");
					sb.append(mSelectors[i]);
					sb.append(" ");
					sb.append(mArgumentSorts[i]);
					sb.append(")");
				}
			}
			sb.append(")");
			return sb.toString();
		}
	}

	public DataType(final Theory theory, final String name, final int numParams) {
		super(theory, name, numParams, null, DATATYPE);
	}

	/**
	 * The constructors.
	 */
	Constructor[] mConstructors;
	/**
	 * The generic sort arguments.
	 */
	Sort[] mSortVariables;

	public void setConstructors(final Sort[] sortVars, final Constructor[] constrs) {
		assert mConstructors == null;
		mSortVariables = sortVars;
		mConstructors = constrs;
		if (sortVars != null) {
			for (final Constructor cons : constrs) {
				cons.mNeedsReturnOverload = checkReturnOverload(sortVars, cons.mArgumentSorts);
			}
		}
	}

	public Sort[] getSortVariables() {
		return mSortVariables;
	}

	public Constructor findConstructor(final String name) {
		for (int i = 0; i < mConstructors.length; i++) {
			if (mConstructors[i].getName().equals(name)) {
				return mConstructors[i];
			}
		}
		return null;
	}

	public Constructor getConstructor(final String name) {
		final Constructor constr = findConstructor(name);
		if (constr == null) {
			throw new NoSuchElementException();
		}
		return constr;
	}

	public Constructor[] getConstructors() {
		return mConstructors;
	}

	/**
	 * Check if a constructor of a datatype needs to be declared with
	 * RETURNOVERLOAD. This is the case if its arguments do not contain all sort
	 * parameters.
	 *
	 * @param sortParams    The sort parameters of the datatype.
	 * @param argumentSorts The arguments of the constructor.
	 * @return 0 or RETURNOVERLOAD, depending on if the flag is needed.
	 */
	private boolean checkReturnOverload(final Sort[] sortParams, final Sort[] argumentSorts) {
		final BitSet unused = new BitSet();
		unused.set(0, sortParams.length);
		final ArrayDeque<Sort> todo = new ArrayDeque<>();
		final HashSet<Sort> seen = new HashSet<>();
		todo.addAll(Arrays.asList(argumentSorts));
		while (!todo.isEmpty()) {
			final Sort sort = todo.removeFirst();
			if (seen.add(sort)) {
				if (sort.isSortVariable()) {
					for (int i = 0; i < sortParams.length; i++) {
						if (sort == sortParams[i]) {
							unused.clear(i);
							break;
						}
					}
				} else {
					todo.addAll(Arrays.asList(sort.getArguments()));
				}
			}
		}
		return !unused.isEmpty();
	}
}
