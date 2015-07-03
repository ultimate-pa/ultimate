package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain;

import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BinaryExpression.Operator;

/**
 * Interface for NAry evaluators that have some operator.
 * 
 * @author greitsch@informatik.uni-freiburg.de
 */
public interface INAryEvaluator<T, ACTION, VARDECL> extends IEvaluator<T, ACTION, VARDECL>{
	
	public void setOperator(Object operator);
}
