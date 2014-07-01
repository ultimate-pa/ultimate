package de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates;

import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;

/**
 * @author heizmann@informatik.uni-freiburg.de
 *
 */
public interface IPredicate  {

	public String[] getProcedures();

	public Term getFormula();
	
	public Term getClosedFormula();

	public Set<BoogieVar> getVars();
	
}