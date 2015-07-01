package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain;

import java.util.Set;

/**
 * Default interface for an expression evaluator. Each Evaluator should implement this interface in order to allow for
 * expressions to be evaluated.
 * 
 * @author greitsch@informatik.uni-freiburg.de
 */
public interface IEvaluator<T, ACTION, VARDECL> {

	public IEvaluationResult<?> evaluate(IAbstractState<?, ?> currentState);

	public void addSubEvaluator(IEvaluator<?, ?, ?> evaluator);

	public Set<String> getVarIdentifiers();
	
	public boolean hasFreeOperands();
	
	public Class<T> getType();
}
