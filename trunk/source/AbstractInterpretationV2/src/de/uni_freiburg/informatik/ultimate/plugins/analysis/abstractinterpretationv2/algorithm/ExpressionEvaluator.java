package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm;

import java.util.Stack;

import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.IEvaluator;

/**
 * Enables the construction and evaluation of multiple {@link IEvaluator}s. It is assumed that the order, in which an
 * abstract syntax tree is traversed to build the different evaluators is pre-order depth-first search where the
 * left-most child element is being evaluated first.
 * 
 * @author greitsch@informatik.uni-freiburg.de
 *
 */
public class ExpressionEvaluator<T, ACTION, VARDECL> {

	private Stack<IEvaluator<?, ?, ?>> mEvaluators;
	private IEvaluator<?, ?, ?> mRootEvaluator;

	/**
	 * The default constructor.
	 */
	public ExpressionEvaluator() {
		mEvaluators = new Stack<IEvaluator<?, ?, ?>>();
		mRootEvaluator = null;
	}

	/**
	 * Adds a new {@link IEvaluator} to the already existing ones and builds an evaluator tree that defines the order in
	 * which each {@link IEvaluator} should be evaluated. If there is no evaluator present yet, this function will store
	 * the first evaluator as a root element which can be retrieved by {@link ExpressionEvaluator#getRootEvaluator()}.
	 * 
	 * @param evaluator
	 */
	public void addEvaluator(IEvaluator<?, ?, ?> evaluator) {

		// TODO Insert sanity checks to be on the safe side.

		if (mEvaluators.isEmpty()) {
			mEvaluators.push((IEvaluator<T, ACTION, VARDECL>) evaluator);
			mRootEvaluator = (IEvaluator<T, ACTION, VARDECL>) evaluator;
		} else {
			if (mEvaluators.peek().hasFreeOperands()) {
				mEvaluators.peek().addSubEvaluator(evaluator);
				if (evaluator.hasFreeOperands()) {
					mEvaluators.push(evaluator);
				}
			}
		}

		// Pop off all the elements that do not have free operands anymore
		while (!mEvaluators.isEmpty()) {
			if (!mEvaluators.peek().hasFreeOperands()) {
				mEvaluators.pop();
			} else {
				break;
			}
		}
	}

	/**
	 * Returns the root evaluator of the evaluation tree.
	 * 
	 * @return
	 */
	public IEvaluator<?, ?, ?> getRootEvaluator() {
		return mRootEvaluator;
	}

	/**
	 * Returns <code>true</code> if there are no evaluators present in the {@link ExpressionEvaluator},
	 * <code>false</code> otherwise.
	 * 
	 * @return
	 */
	public boolean isEmpty() {
		return mEvaluators.isEmpty();
	}

	/**
	 * Returns <code>true</code> if all added {@link IEvaluator}s have been assembled completely. The root of the
	 * evaluation tree can be obtained via {@link ExpressionEvaluator#getRootEvaluator()}. Returns <code>false</code>
	 * otherwise.
	 * 
	 * @return
	 */
	public boolean isFinished() {
		return isEmpty() && (mRootEvaluator != null);
	}
}
