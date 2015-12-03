package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.abstractdomain;

import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Boogie2SMT;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.AbstractVariable;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.TypedAbstractVariable;

/**
 * Abstract State, representing a valuation for all variables of a program
 * state's scope to an abstract value space
 * 
 * @author GROSS-JAN
 *
 * @param <T>
 *            the concrete type of the state
 */
public interface IAbstractState<T> {
	/**
	 * Returns true if this state is greater or eual than the given state
	 * 
	 * @param state
	 * @return
	 */
	boolean isSuperOrEqual(IAbstractState<?> state);

	/**
	 * Determines whether a variable is declared in this state or not.
	 * 
	 * @param variable
	 * @return
	 */
	boolean hasVariable(AbstractVariable variable);

	/**
	 * This is called if a new variable is present.
	 * 
	 * @param variable
	 */
	void declareVariable(TypedAbstractVariable variable);

	/**
	 * This must return the typed variable instance with declaration
	 * information.
	 * 
	 * @param variable
	 */
	TypedAbstractVariable getTypedVariable(AbstractVariable variable);

	/**
	 * Determines whether a variable is declared in this state or not.
	 * 
	 * @param variable
	 */
	void removeVariable(AbstractVariable variable);

	/**
	 * 
	 * @return
	 */
	IAbstractState<T> copy();

	/**
	 * This returns true if the this state has no reachable valuations.
	 * 
	 * @return
	 */
	boolean isBottom();

	/**
	 * Returns the instance as the inner type.
	 * 
	 * @return
	 */
	T getConcrete();

	/**
	 * Create SMT constraint from this abstract state.
	 * 
	 * @param script
	 * @param bpl2smt
	 * @return
	 */
	Term getTerm(Script script, Boogie2SMT bpl2smt);	
}
