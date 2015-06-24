package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm;

import java.util.Stack;

import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.IEvaluator;

/**
 * 
 * 
 * @author greitsch@informatik.uni-freiburg.de
 *
 */
public class ExpressionEvaluator<T, ACTION, VARDECL> {
	Stack<IEvaluator<T, ACTION, VARDECL>> mEvaluators;

	public ExpressionEvaluator() {
		mEvaluators = new Stack<IEvaluator<T, ACTION, VARDECL>>();
	}

	public void addEvaluator(IEvaluator<T, ACTION, VARDECL> evaluator) {
		
		if (mEvaluators.isEmpty()) {
			mEvaluators.push(evaluator);
			return;
		}
		
		if (mEvaluators.peek().hasFreeOperands()) {
			mEvaluators.peek().addSubEvaluator(evaluator);
			if (evaluator.hasFreeOperands()) {
				mEvaluators.push(evaluator);
			}
			return;
		}
		
		mEvaluators.push(evaluator);
	}
}
