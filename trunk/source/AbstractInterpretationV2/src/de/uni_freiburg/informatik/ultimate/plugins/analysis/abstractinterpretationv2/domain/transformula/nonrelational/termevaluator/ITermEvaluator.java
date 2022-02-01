package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.nonrelational.termevaluator;

import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractState;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.evaluator.IEvaluationResult;

public interface ITermEvaluator<VALUE, STATE extends IAbstractState<STATE>> {
	List<IEvaluationResult<VALUE>> evaluate(final STATE currentState);

	List<STATE> inverseEvaluate(final IEvaluationResult<VALUE> evaluationResult, final STATE state);

	void addSubEvaluator(final ITermEvaluator<VALUE, STATE> evaluator);

	boolean hasFreeOperands();

	boolean containsBool();

	Set<String> getVarIdentifiers();
}
