package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.nonrelational.termevaluator;

import java.util.ArrayList;
import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.absint.IAbstractState;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.evaluator.EvaluatorUtils.EvaluatorType;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.evaluator.IEvaluationResult;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.evaluator.IEvaluator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.evaluator.INAryEvaluator;

public class LogicalTermEvaluator<VALUE, STATE extends IAbstractState<STATE, VARDECL>, VARDECL>
		implements INAryEvaluator<VALUE, STATE, VARDECL> {
	
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
	public void addSubEvaluator(final IEvaluator<VALUE, STATE, VARDECL> evaluator) {
		if (mSubEvaluators.size() >= mArity) {
			throw new UnsupportedOperationException("Too many sub evaluators for n-ary evaluator of size " + mArity);
		}
		
		mSubEvaluators.add(evaluator);
	}
	
	@Override
	public Set<VARDECL> getVarIdentifiers() {
		// TODO Auto-generated method stub
		return null;
	}
	
	@Override
	public boolean hasFreeOperands() {
		return mSubEvaluators.size() < mArity;
	}
	
	@Override
	public boolean containsBool() {
		return mSubEvaluators.stream().anyMatch(e -> e.containsBool());
	}
	
	@Override
	public EvaluatorType getType() {
		// TODO
		return null;
	}
	
	@Override
	public void setOperator(final Object operator) {
		// TODO Auto-generated method stub

	}
	
	@Override
	public int getArity() {
		// TODO Auto-generated method stub
		return 0;
	}

}
