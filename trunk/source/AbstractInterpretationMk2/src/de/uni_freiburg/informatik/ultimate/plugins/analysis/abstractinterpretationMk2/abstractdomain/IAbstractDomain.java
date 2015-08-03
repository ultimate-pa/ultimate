package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.abstractdomain;

import de.uni_freiburg.informatik.ultimate.model.IType;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.AssumeStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.HavocStatement;



/**
 * 
 * @author GROSS-JAN
 *
 * @param <T> concrete type of abstract states
 */
public interface IAbstractDomain<T> 
{	
	void setMergeOperator(IAbstractMergeOperator<T> mergeOperator);
	void setWideningOperator(IAbstractWideningOperator<T> wideningOperator);
	
	IAbstractMergeOperator<T> getMergeOperator();
	IAbstractWideningOperator<T> getWideningOperator();
	
	IAbstractState<T> createState();
	
	IAbstractState<T> createBottom();
	IAbstractState<T> createTop();
	
	/**
	 * Manifests the expression in the given target variable
	 * as a statement
	 * target = exp
	 * The resulting state should be the same reference as the given,
	 * but it can be replaced if convenient.
	 * If it is necessary to copy it, the state must be copied by the
	 * caller.
	 * 
	 * 
	 * @param state
	 * @param target
	 * @param exp
	 * @return
	 */
	IAbstractState<T> ApplyExpression(IAbstractState<T> state, AbstractVariable target, IType targetType, Expression exp);
	
	
	/**
	 * Havocs the given target variable in the given state.
	 * target = [top]
	 * The resulting state should be the same reference as the given,
	 * but it can be replaced if convenient.
	 * If it is necessary to copy it, the state must be copied by the
	 * caller.
	 * 
	 * 
	 * @param state
	 * @param target
	 * @param exp
	 * @return
	 */
	IAbstractState<T> ApplyHavoc(IAbstractState<T> state, AbstractVariable target, IType targetType);
	
	
	/**
	 * Applies the assume in the given state, cuts out everyting of the
	 * state which is not fullfilling the given expression. 
	 * The resulting state should be the same reference as the given,
	 * but it can be replaced if convenient.
	 * If it is necessary to copy it, the state must be copied by the
	 * caller.
	 * 
	 * @param state
	 * @param exp
	 * @return
	 */
	IAbstractState<T> ApplyAssume(IAbstractState<T> state, Expression exp);
	
	
	/**
	 * Checks if the given expression evaluates not to false.
	 * 
	 * @param state
	 * @param exp
	 * @return
	 */
	boolean ApplyAssert(IAbstractState<T> state, Expression exp);
}
