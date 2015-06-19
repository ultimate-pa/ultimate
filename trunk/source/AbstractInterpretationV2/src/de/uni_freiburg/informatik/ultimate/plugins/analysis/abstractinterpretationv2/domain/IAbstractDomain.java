package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain;

/**
 * 
 * @author dietsch@informatik.uni-freiburg.de
 * @author greitsch@informatik.uni-freiburg.de
 *
 */
public interface IAbstractDomain<STATE extends IAbstractState<ACTION, VARDECL>, ACTION, VARDECL> {
	IAbstractState<ACTION, VARDECL> createFreshState();

	IAbstractStateBinaryOperator<ACTION, VARDECL> getWideningOperator();

	IAbstractStateBinaryOperator<ACTION, VARDECL> getMergeOperator();

	IAbstractPostOperator<ACTION, VARDECL> getPostOperator();

	Class<STATE> getAbstractStateClass();
}
