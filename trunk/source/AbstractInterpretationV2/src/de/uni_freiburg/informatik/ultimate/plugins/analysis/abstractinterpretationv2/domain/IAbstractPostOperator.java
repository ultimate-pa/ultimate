package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain;

/**
 * 
 * @author dietsch@informatik.uni-freiburg.de
 * @author greitsch@informatik.uni-freiburg.de
 * 
 */
public interface IAbstractPostOperator<ACTION, VARDECL> {

	IAbstractState<ACTION, VARDECL> apply(IAbstractState<ACTION, VARDECL> oldstate, ACTION concrete);

}
