package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.nonrelational.termevaluator;

import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.absint.IAbstractState;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.evaluator.IEvaluationResult;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.evaluator.IEvaluator;

public class LogicalTermEvaluator<VALUE, STATE extends IAbstractState<STATE, VARDECL>, VARDECL>
		implements INaryTermEvaluator<VALUE, STATE, VARDECL> {
	
	private final int mArity;
	private final String mType;
	private final ILogger mLogger;

	private final List<IEvaluator<VALUE, STATE, VARDECL>> mSubEvaluators;
	
	protected LogicalTermEvaluator(final int arity, final String type, final ILogger logger) {
		mArity = arity;
		mType = type;
		mLogger = logger;
		mSubEvaluators = new ArrayList<>(arity);
	}

	@Override
	public List<IEvaluationResult<VALUE>> evaluate(final STATE currentState) {
		// TODO Auto-generated method stub
		return null;
	}
	
	@Override
	public List<STATE> inverseEvaluate(final IEvaluationResult<VALUE> evalResult, final STATE state) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public void addSubEvaluator(final ITermEvaluator<VALUE, STATE, VARDECL> evaluator) {
		// TODO Auto-generated method stub
		
	}

	@Override
	public boolean hasFreeOperands() {
		// TODO Auto-generated method stub
		return false;
	}

	@Override
	public boolean containsBool() {
		// TODO Auto-generated method stub
		return false;
	}

	@Override
	public void setOperator(final String operator) {
		// TODO Auto-generated method stub
		
	}

	@Override
	public int getArity() {
		// TODO Auto-generated method stub
		return 0;
	}

	protected enum LogicalTypes {
		AND, OR, XOR, NOT, GEQ
	}
}
