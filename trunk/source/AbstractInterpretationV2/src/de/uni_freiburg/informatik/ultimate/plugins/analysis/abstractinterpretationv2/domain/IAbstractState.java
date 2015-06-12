package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain;

/**
 * 
 * @author dietsch@informatik.uni-freiburg.de
 * @author greitsch@informatik.uni-freiburg.de
 *
 * @param <ACTION>
 * @param <VARDECL>
 */
public interface IAbstractState<ACTION, VARDECL> {

	void addVariables(VARDECL variables);

	void removeVariables(VARDECL variables);

	void addVariables(VARDECL[] variables);

	void removeVariables(VARDECL[] variables);

	ComparisonResult compareTo(IAbstractState<ACTION, VARDECL> other);
	
	boolean isBottom();
	
	boolean isFixpoint();
	
	void setFixpoint(boolean value);

	public enum ComparisonResult {
		SUPER, SUB, EQUAL, NOTEQUAL
	}
}
