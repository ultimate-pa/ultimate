package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain;

/**
 * Interface to create IEvaluators for different abstract domains.
 * 
 * @author greitsch@informatik.uni-freiburg.de
 *
 */
public interface IEvaluatorFactory<T, ACTION, VARDECL> {
	public IEvaluator<T, ACTION, VARDECL> createNAryExpressionEvaluator(int arity);
	public IEvaluator<T, ACTION, VARDECL> createSingletonValueExpressionEvaluator();
	public IEvaluator<T, ACTION, VARDECL> createSingletonVariableExpressionEvaluator();
}