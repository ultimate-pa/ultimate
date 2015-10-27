package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.abstractdomain;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.TypedAbstractVariable;

/**
 * 
 * @author GROSS-JAN
 *
 * @param <T>
 *            concrete type of abstract states
 */
public interface IAbstractDomain<T> {
	void setMergeOperator(IAbstractMergeOperator<T> mergeOperator);

	void setWideningOperator(IAbstractWideningOperator<T> wideningOperator);

	IAbstractMergeOperator<T> getMergeOperator();

	IAbstractWideningOperator<T> getWideningOperator();

	IAbstractState<T> createState();

	// IAbstractState<T> createBottom();
	// IAbstractState<T> createTop();

	/**
	 * Manifests the expression in the given target variable as a statement
	 * target = exp The resulting state should be the same reference as the
	 * given, but it can be replaced if convenient. So if it is necessary to
	 * copy it, the state must be copied by the caller)
	 * 
	 * 
	 * @param state
	 * @param target
	 *            the variable where the value will be havoced. Here we need
	 *            declaration information since the variable may not be present
	 *            in the state yet
	 * @param exp
	 * @return
	 */
	IAbstractState<T> applyExpression(IAbstractState<T> state,
			TypedAbstractVariable target, Expression exp);

	/**
	 * Havocs the given target variable in the given state. target = [top] The
	 * resulting state should be the same reference as the given, but it can be
	 * replaced if convenient. If it is necessary to copy it, the state must be
	 * copied by the caller.
	 * 
	 * @param state
	 * @param target
	 *            the variable where the value will be havoced. Here we need
	 *            declaration information since the variable may not be present
	 *            in the state yet
	 * @param exp
	 * @return
	 */
	IAbstractState<T> applyHavoc(IAbstractState<T> state,
			TypedAbstractVariable target);

	/**
	 * Applies the assume in the given state, cuts out everything of the state
	 * which is not fulfilling the given expression. The resulting state should
	 * be the same reference as the given, but it can be replaced if convenient.
	 * If it is necessary to copy it, the state must be copied by the caller. An
	 * assume statement may lead to multiple states if there is an non-negative
	 * or-operator (or something logically equivalent). There will be two states
	 * 
	 * @param state
	 * @param exp
	 * @return
	 */
	List<IAbstractState<T>> applyAssume(IAbstractState<T> state, Expression exp);

	/**
	 * Applies a call or return into target state. In targetState the given
	 * variables must be written with the given arguments. But the valuation of
	 * the argument expressions must be evaluated from oldState. Old state shall
	 * not be changed
	 * 
	 * @param targetState
	 *            The state where the expressions have to be manifested
	 * @param oldState
	 *            The state from which the values of arguments must be taken
	 *            (must not be changed)
	 * @param targts
	 *            The variables to be overridden by the given arguments in
	 *            newState
	 * @param arguments
	 *            Expressions which should be evaluated using oldState
	 * @return
	 */
	void applyExpressionScoped(IAbstractState<T> targetState,
			IAbstractState<T> oldState, List<TypedAbstractVariable> targets,
			List<Expression> arguments);

	/**
	 * Checks if the given expression evaluates not to false.
	 * 
	 * @param state
	 * @param exp
	 * @return
	 */
	boolean checkAssert(IAbstractState<T> state, Expression exp);
	
	/**
	 * Initializes the abstract domain.
	 */
	public void initializeDomain();
	
	/**
	 * Finalizes the abstract domain.
	 */
	public void finalizeDomain();
}
