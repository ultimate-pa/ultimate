package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain;

/**
 * 
 * @author dietsch@informatik.uni-freiburg.de
 * @author greitsch@informatik.uni-freiburg.de
 * 
 */
public interface IAbstractStateBinaryOperator<ACTION, VARDECL> {

	IAbstractState<ACTION, VARDECL> apply(IAbstractState<ACTION, VARDECL> first,
			IAbstractState<ACTION, VARDECL> second);

}
