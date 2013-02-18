package de.uni_freiburg.informatik.ultimate.plugins.generator.rankingfunctions.functions;

import java.io.Serializable;
import java.util.*;

import de.uni_freiburg.informatik.ultimate.logic.*;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Smt2Boogie;

/**
 * A ranking function is a function that proves termination for a given program.
 * 
 * @author Jan Leike
 */
public interface RankingFunction extends Serializable {
	/**
	 * Return a string representation of the ranking function. 
	 */
	public String toString();
	
	/**
	 * Evaluate the ranking function
	 * @param assignment the variable assignment
	 * @return value of the function
	 */
	public Rational evaluate(Map<BoogieVar, Rational> assignment);
	
	/**
	 * Return the ranking function in form of a SMTLib term.
	 * @param script the current script
	 * @return ranking function as boolean term
	 */
	public Term asFormula(Script script, Smt2Boogie smt2boogie)
			throws SMTLIBException;
}
