package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.nonrelational.termevaluator;

import de.uni_freiburg.informatik.ultimate.modelcheckerutils.absint.IAbstractState;

public interface INaryTermEvaluator<VALUE, STATE extends IAbstractState<STATE, VARDECL>, VARDECL>
		extends ITermEvaluator<VALUE, STATE, VARDECL> {
	void setOperator(String operator);
	
	int getArity();
}
