package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain;

import java.util.Map;

/**
 * 
 * @author dietsch@informatik.uni-freiburg.de
 * @author greitsch@informatik.uni-freiburg.de
 *
 * @param <ACTION>
 * @param <VARDECL>
 */
public interface IAbstractState<ACTION, VARDECL> {

	IAbstractState<ACTION, VARDECL> addVariable(String name, VARDECL variables);

	IAbstractState<ACTION, VARDECL> removeVariable(String name, VARDECL variables);

	IAbstractState<ACTION, VARDECL> addVariables(Map<String, VARDECL> variables);

	IAbstractState<ACTION, VARDECL> removeVariables(Map<String, VARDECL> variables);

	boolean containsVariable(String name);

	/**
	 * An abstract state is empty when it does not contain any variable.
	 * 
	 * @return true iff this abstract state is empty
	 */
	boolean isEmpty();

	boolean isBottom();

	boolean isFixpoint();

	IAbstractState<ACTION, VARDECL> setFixpoint(boolean value);

	String toLogString();

	boolean isEqualTo(IAbstractState<ACTION, VARDECL> other);

	IAbstractState<ACTION, VARDECL> copy();
}
