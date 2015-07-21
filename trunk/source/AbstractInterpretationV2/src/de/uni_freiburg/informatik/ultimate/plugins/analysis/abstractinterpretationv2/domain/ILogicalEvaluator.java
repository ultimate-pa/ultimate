package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain;

/**
 * Extends the IEvaluator by the function computeLogicalResult which is used to return new abstract states based on the
 * logical evaluation of the evaluator.
 * 
 * @author greitsch@informatik.uni-freiburg.de
 *
 * @param <T>
 *            Any type.
 * @param <ACTION>
 *            Any action.
 * @param <VARDECL>
 *            Any variable declaration.
 */
public interface ILogicalEvaluator<T, ACTION, VARDECL> extends INAryEvaluator<T, ACTION, VARDECL> {

	public IAbstractState<ACTION, VARDECL> logicallyInterpret(IAbstractState<ACTION, VARDECL> currentState);
	
	public boolean logicalEvaluation(IAbstractState<ACTION, VARDECL> currentState);
}
