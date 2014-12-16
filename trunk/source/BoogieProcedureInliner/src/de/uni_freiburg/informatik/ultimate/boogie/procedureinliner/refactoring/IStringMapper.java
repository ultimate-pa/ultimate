package de.uni_freiburg.informatik.ultimate.boogie.procedureinliner.refactoring;

public interface IStringMapper {

	/**
	 * Maps variable names to other variable names.
	 * @param oldVarName Variable name as it occurred in the expression
	 * @return New name for this occurrence of this variable.
	 */
	public String map(String oldVarName);
}
