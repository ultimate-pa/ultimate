/*
 * Copyright (C) 2012-2014 University of Freiburg
 *
 * This file is part of the ULTIMATE LassoRanker Library.
 *
 * The ULTIMATE LassoRanker Library is free software: you can redistribute it
 * and/or modify it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation, either version 3 of the
 * License, or (at your option) any later version.
 *
 * The ULTIMATE LassoRanker Library is distributed in the hope that it will
 * be useful, but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE LassoRanker Library. If not,
 * see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE LassoRanker Library, or any covered work, by
 * linking or combining it with Eclipse RCP (or a modified version of
 * Eclipse RCP), containing parts covered by the terms of the Eclipse Public
 * License, the licensors of the ULTIMATE LassoRanker Library grant you
 * additional permission to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lassoranker.termination.rankingfunctions;

import java.io.Serializable;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lassoranker.variables.RankVar;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Term2Expression;


/**
 * A ranking function is a function that proves termination for a given program.
 * 
 * @author Jan Leike
 */
public abstract class RankingFunction implements Serializable {
	private static final long serialVersionUID = 4774387985755366720L;
	
	/**
	 * @return Name of this ranking function (e.g., affine, 2-phase, 3-nesting)
	 */
	public abstract String getName();
	
	/**
	 * @return the set of all variables occurring in the ranking function
	 */
	public abstract Set<RankVar> getVariables();
	
	/**
	 * Evaluate the ranking function
	 * @param assignment the variable assignment
	 * @return value of the function as an ordinal
	 */
	public abstract Ordinal evaluate(Map<RankVar, Rational> assignment);
	
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
	public Expression[] asLexExpression(Script script, Term2Expression term2expr) {
		Term[] lex = this.asLexTerm(script);
		Expression[] lexExpressions = new Expression[lex.length];
		for (int i = 0; i < lex.length; ++i) {
			lexExpressions[i] = term2expr.translate(lex[i]);
		}
		return lexExpressions;
	}
}
