package de.uni_freiburg.informatik.ultimate.logic;

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

		public Constructor(String name, String[] selectors, Sort[] argumentSorts) {
			this.mName = name;
			this.mSelectors = selectors;
			this.mArgumentSorts = argumentSorts;
		}

		public String getName() {
			return mName;
		}

		public Sort[] getArgumentSorts() {
			return mArgumentSorts;
		}

		public String[] getSelectors() {
			return mSelectors;
		}

		public String toString() {
			StringBuilder sb = new StringBuilder();
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

	public DataType(Theory theory, String name, int numParams) {
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

	public void setConstructors(Sort[] sortVars, Constructor[] constrs) {
		assert mConstructors == null;
		mSortVariables = sortVars;
		mConstructors = constrs;
	}

	public Sort[] getSortVariables() {
		return mSortVariables;
	}

	public Constructor findConstructor(String name) {
		for (int i = 0; i < mConstructors.length; i++) {
			if (mConstructors[i].getName().equals(name)) {
				return mConstructors[i];
			}
		}
		return null;
	}

	public Constructor[] getConstructors() {
		return mConstructors;
	}
}
