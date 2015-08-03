package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.abstractdomain;


/**
 * Abstract State, representing a valuation for all variables
 * of a program state's scope to an abstract value space
 * 
 * @author GROSS-JAN
 *
 * @param <T> the concrete type of the state
 */
public interface IAbstractState<T> 
{
	boolean isSuper(IAbstractState<T> state);
	
	void DeclareVariable(AbstractVariable variable);
	
	void RemoveVariable(AbstractVariable variable);
	
	IAbstractState<T> copy();

	boolean isBottom();
	
	boolean isTop();
		
	T getConcrete();
}
