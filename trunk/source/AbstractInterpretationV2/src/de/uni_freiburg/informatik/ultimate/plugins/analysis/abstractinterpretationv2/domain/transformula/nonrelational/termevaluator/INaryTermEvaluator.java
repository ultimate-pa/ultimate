package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.nonrelational.termevaluator;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractState;

public interface INaryTermEvaluator<VALUE, STATE extends IAbstractState<STATE>> extends ITermEvaluator<VALUE, STATE> {

	/**
	 * @return The arity of the n-ary evaluator.
	 */
	int getArity();
}
