package de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.rankingfunctions;

import java.io.Serializable;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Smt2Boogie;

/**
 * A ranking function is a function that proves termination for a given program.
 * 
 * @author Jan Leike
 */
public abstract class RankingFunction implements Serializable {
	private static final long serialVersionUID = 4774387985755366720L;
	
	/**
	 * @return the set of all variables occurring in the ranking function
	 */
	public abstract Set<BoogieVar> getVariables();
	
	/**
	 * Evaluate the ranking function
	 * @param assignment the variable assignment
	 * @return value of the function as an ordinal
	 */
	public abstract Ordinal evaluate(Map<BoogieVar, Rational> assignment);
	
	/**
	 * Return the ranking function as a lexicographically ordered list of
	 * SMTLib terms, with the highest component being the list's first item.
	 * The length of this list is asserted to be constant throughout the
	 * lifetime of this object.
	 * 
	 * @param script the current script
	 */
	public abstract Term[] asLexTerm(Script script) throws SMTLIBException;
	
	/**
	 * Return the ranking function as a Boogie AST expression
	 * @param script the current script
	 * @param smt2boogie the variable translation
	 * @return ranking function as boolean term
	 */
	public Expression[] asLexExpression(Script script, Smt2Boogie smt2boogie) {
		Term[] lex = this.asLexTerm(script);
		Expression[] lexExpressions = new Expression[lex.length];
		for (int i = 0; i < lex.length; ++i) {
			lexExpressions[i] = smt2boogie.translate(lex[i]);
		}
		return lexExpressions;
	}
}
