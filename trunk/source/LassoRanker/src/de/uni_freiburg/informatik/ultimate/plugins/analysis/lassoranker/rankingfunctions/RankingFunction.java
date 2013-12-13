package de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.rankingfunctions;

import java.io.Serializable;
import java.util.*;

import de.uni_freiburg.informatik.ultimate.logic.*;
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
	 * Evaluate the ranking function
	 * @param assignment the variable assignment
	 * @return value of the function as an ordinal
	 */
	public abstract Ordinal evaluate(Map<BoogieVar, Rational> assignment);
	
	/**
	 * Return the ranking function as a lexicographically ordered list of
	 * SMTLib terms, with the highest entry being the first.
	 * The length of this list is asserted to be constant throughout the
	 * lifetime of this object.
	 * @param script the current script
	 */
	public abstract List<Term> asLexTerm(Script script) throws SMTLIBException;
	
	/**
	 * Return the ranking function as a Boogie AST expression
	 * @param script the current script
	 * @param smt2boogie the variable translation
	 * @return ranking function as boolean term
	 */
	public List<Expression> asLexExpression(Script script, Smt2Boogie smt2boogie) {
		List<Term> lex = this.asLexTerm(script);
		List<Expression> lexExpressions = new ArrayList<Expression>();
		for (Term term : lex) {
			lexExpressions.add(smt2boogie.translate(term));
		}
		return lexExpressions;
	}
}
