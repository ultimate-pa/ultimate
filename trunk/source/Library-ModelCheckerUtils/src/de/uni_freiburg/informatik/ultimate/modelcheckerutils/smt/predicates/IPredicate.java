package de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates;

import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;

/**
 * Represents a set of program states.
 * 
 * 
 * @author heizmann@informatik.uni-freiburg.de
 *
 */
public interface IPredicate  {

	public String[] getProcedures();

	public Term getFormula();
	
	public Term getClosedFormula();

	/**
	 * Returns a superset of the all BoogieVars whose corresponding
	 * TermVariable occurs in the formula of this IPredicate.
	 */
	public Set<BoogieVar> getVars();
	
}