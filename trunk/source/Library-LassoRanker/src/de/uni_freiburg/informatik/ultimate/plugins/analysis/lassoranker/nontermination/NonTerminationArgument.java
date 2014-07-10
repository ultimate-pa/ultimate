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
package de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.nontermination;

import java.io.Serializable;
import java.util.Collections;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Term2Expression;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.variables.RankVar;


/**
 * Represents a non-termination argument for a lasso program in form of an
 * infinite execution.
 * 
 * It is composed of
 * <ul>
 * <li> an initial state at the begin of the lasso,
 * <li> a state at first visit of the honda,
 * <li> a ray of the loop's transition polyhedron, and
 * <li> a discount factor lambda.
 * </ul>
 * 
 * The infinite execution described by this nontermination argument is
 * 
 * state_init, state_honda,
 * state_honda + ray, state_honda + (1 + lambda) ray,
 * state_honda + (1 + lambda + lambda^2) ray, ...
 * 
 * @author Jan Leike
 */
public class NonTerminationArgument implements Serializable {
	private static final long serialVersionUID = 4606815082909883553L;
	
	private final Map<RankVar, Rational> m_StateInit;
	private final Map<RankVar, Rational> m_StateHonda;
	private final Map<RankVar, Rational> m_Ray;
	private final Rational m_Lambda;
	
	/**
	 * Construct a non-termination argument
	 * 
	 * The infinite execution described by this nontermination argument is
	 * 
	 * state_init, state_honda,
	 * state_honda + ray, state_honda + (1 + lambda) ray,
	 * state_honda + (1 + lambda + lambda^2) ray, ...
	 * 
	 * @param state_init initial state
	 * @param state_honda state at the lasso's honda
	 * @param ray ray of the lasso's polyhedron
	 * @param lambda discount factor
	 */
	public NonTerminationArgument(Map<RankVar, Rational> state_init,
			Map<RankVar, Rational> state_honda,
			Map<RankVar, Rational> ray,
			Rational lambda) {
		assert(state_init != null);
		m_StateInit = state_init;
		assert(state_honda != null);
		m_StateHonda = state_honda;
		assert(lambda != null);
		m_Lambda = lambda;
		assert(ray != null);
		m_Ray = ray;
	}
	
	/**
	 * @return the initial state
	 */
	public Map<RankVar, Rational> getStateInit() {
		return Collections.unmodifiableMap(m_StateInit);
	}
	
	/**
	 * @return the state at the lasso's honda
	 */
	public Map<RankVar, Rational> getStateHonda() {
		return Collections.unmodifiableMap(m_StateHonda);
	}
	
	/**
	 * @return the ray of the loop's transition polyhedron 
	 */
	public Map<RankVar, Rational> getRay() {
		return Collections.unmodifiableMap(m_Ray);
	}
	
	/**
	 * Translate a sequence of mappings from RankVars to Rationals into a 
	 * sequence of mappings from Expressions to Rationals.
	 * The RanksVars are translated into an Expressions that represents the
	 * defining term of the RankVar. The Rationals are are translated to 1 
	 * (true) and 0 (false) if the corresponding RankVar represented a Term
	 * of sort Bool.
	 * Ensures that RankVars that are defined by equivalent terms translated 
	 * to the same Expression object. 
	 */
	public static Map<Expression, Rational>[] rank2Boogie(
			Term2Expression term2expression,
			Map<RankVar, Rational>... states) {
		Map<Expression, Rational>[] result = new Map[states.length];
		Map<Term, Expression> rankVar2Expression = 
				new HashMap<Term, Expression>();
		for (int i=0; i<states.length; i++) {
			Map<Expression, Rational> expression2rational =
					new LinkedHashMap<Expression, Rational>();
			for (Map.Entry<RankVar, Rational> entry : states[i].entrySet()) {
				RankVar rv = entry.getKey();
				Expression e;
				if (rankVar2Expression.containsKey(rv.getDefinition())) {
					e = rankVar2Expression.get(rv.getDefinition());
				} else {
					e = rankVar2Expression(rv, term2expression);
					rankVar2Expression.put(rv.getDefinition(), e);
				}
				Rational r = entry.getValue();
				// Replace Rational for boolean RankVars
				if (rv.getDefinition().getSort().getName().equals("Bool")) {
					// value >= 1 means true, which is translated to 1,
					// false is translated to 0.
					r = entry.getValue().compareTo(Rational.ONE) == -1 ?
							Rational.ONE : Rational.ZERO;
				}
				assert e != null && r != null;
				expression2rational.put(e, r);
			}
			result[i] = expression2rational;
		}
		return result;
	}
	
	/**
	 * Translate a RankVar into a (Boogie) Expression. The Expression is the
	 * (unique) Expression that represents the definition of the RankVar.
	 */
	public static Expression rankVar2Expression(RankVar rv, 
			Term2Expression term2expression) {
		return term2expression.translate(rv.getDefinition());
	}
	
	
	
	/**
	 * @return the discount factor
	 */
	public Rational getLambda() {
		return m_Lambda;
	}
	
	public String toString() {
		StringBuilder sb = new StringBuilder();
		sb.append("Non-Termination argument consisting of:\n");
		sb.append("Initial state: ");
		sb.append(m_StateInit);
		sb.append("\nHonda state: ");
		sb.append(m_StateHonda);
		sb.append("\nRay: ");
		sb.append(m_Ray);
		sb.append("\nLambda: ");
		sb.append(m_Lambda);
		return sb.toString();
	}
	
//	public Expression asRecurrentSet() {
//		// TODO: { state1, state1 + ray, state1 + (1 + lambda)*ray, ... }
//		return null;
//	}
}
