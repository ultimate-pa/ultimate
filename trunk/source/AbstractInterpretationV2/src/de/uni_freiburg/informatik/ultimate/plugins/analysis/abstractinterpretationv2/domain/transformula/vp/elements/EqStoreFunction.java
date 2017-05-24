package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.logic.Term;

public class EqStoreFunction extends EqFunction {

	private final EqFunction mFunction;
	private final List<EqNode> mIndices;
	private final EqNode mValue;

	public EqStoreFunction(EqFunction function, List<EqNode> indices, EqNode value, Term term, 
			EqNodeAndFunctionFactory factory) {
		super(term, factory);
		mFunction = function;
		mIndices = indices;
		mValue = value;
	}

}
