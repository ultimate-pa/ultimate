package de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt;

import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

/**
 * Interface for the construction of "fresh" TermVariables.
 * In mathematical logics a variable is called "fresh" if the variable has not
 * occurred in the same context.
 * TermVariables constructed by objects that implement this interface are 
 * guaranteed to have a name which is different form all other TermVariables 
 * constructed by this object. There is no guarantee that a similar variable
 * was not constructed with the same Script.
 * @author Matthias Heizmann
 *
 */
public interface IFreshTermVariableConstructor {

	/**
	 * @param name String that will occur as substring of the resulting 
	 * TermVariable.
	 * @param sort Sort of the resulting TermVariable.
	 * @return TermVariable whose name is different from the names
	 * of all other TermVariable that have been constructed by this object.
	 */
	public abstract TermVariable constructFreshTermVariable(String name,
			Sort sort);

}