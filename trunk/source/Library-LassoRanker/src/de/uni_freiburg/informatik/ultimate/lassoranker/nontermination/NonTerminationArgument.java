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
package de.uni_freiburg.informatik.ultimate.lassoranker.nontermination;

import java.io.Serializable;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.lassoranker.variables.RankVar;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Term2Expression;


/**
 * Represents a non-termination argument for a lasso program in form of an
 * infinite execution.
 * 
 * It is composed of
 * <ul>
 * <li> an initial state at the begin of the lasso,
 * <li> a state at first visit of the honda,
 * <li> a list of rays of the loop's transition polyhedron, and
 * <li> a list of discount factors lambda and mu.
 * </ul>
 * 
 * The infinite execution described by this nontermination argument is
 * 
 * <pre>
 * state_init,
 * state_honda,
 * state_honda + ray_1 + ... + ray_n,
 * state_honda + (1 + lambda_1) ray_1 + (1 + lambda_2 + mu_1) ray_2 + ... + (1 + lambda_n + nu_(n-1)) ray_n,
 * ...
 * </pre>
 * 
 * The general form is x + Y*(sum_i J^i)*1 where
 * <ul>
 * <li> x is the initial state
 * <li> Y is a matrix with the rays as columns
 * <li> J is a matrix with lamnbda_i on the diagonal and mu_i on the upper subdiagonal
 * <li> 1 is a column vector of ones
 * </ul>
 * 
 * @author Jan Leike
 */
public class NonTerminationArgument implements Serializable {
	private static final long serialVersionUID = 4606815082909883553L;
	
	private final Map<RankVar, Rational> m_StateInit;
	private final Map<RankVar, Rational> m_StateHonda;
	private final List<Map<RankVar, Rational>> m_Rays;
	private final List<Rational> m_Lambdas;
	private final List<Rational> m_Nus;
	
	/**
	 * Construct a non-termination argument
	 * 
	 * @param state_init initial state
	 * @param state_honda state at the lasso's honda
	 * @param rays rays of the lasso's polyhedron
	 * @param lambdas discount factors
	 * @param nus nilpotent components
	 */
	public NonTerminationArgument(Map<RankVar, Rational> state_init,
			Map<RankVar, Rational> state_honda,
			List<Map<RankVar, Rational>> rays,
			List<Rational> lambdas,
			List<Rational> nus) {
		assert(state_init != null);
		m_StateInit = state_init;
		assert(state_honda != null);
		m_StateHonda = state_honda;
		assert(rays != null);
		m_Rays = rays;
		assert(lambdas != null);
		m_Lambdas = lambdas;
		assert(nus != null);
		m_Nus = nus;
		assert rays.size() == lambdas.size();
		assert rays.size() == nus.size() + 1;
	}
	
	/**
	 * Join the infinite execution of this nontermination argument with
	 * another nontermination argument.
	 * Variables that occur in both nontermination arguments but be assigned
	 * to the same values.
	 * 
	 * This method is used to combine separate arguments that are found
	 * after lasso partitioning.
	 */
	public NonTerminationArgument join(NonTerminationArgument other) {
		// Check for compatibility
		for (RankVar rankVar : m_StateInit.keySet()) {
			if (other.m_StateInit.containsKey(rankVar)) {
				assert m_StateInit.get(rankVar).equals(
						other.m_StateInit.get(rankVar));
			}
		}
		for (RankVar rankVar : m_StateHonda.keySet()) {
			if (other.m_StateHonda.containsKey(rankVar)) {
				assert m_StateHonda.get(rankVar).equals(
						other.m_StateHonda.get(rankVar));
			}
		}
		
		Map<RankVar, Rational> stateInit = new HashMap<RankVar, Rational>();
		Map<RankVar, Rational> stateHonda = new HashMap<RankVar, Rational>();
		List<Map<RankVar, Rational>> rays =
				new ArrayList<Map<RankVar, Rational>>();
		List<Rational> lambdas = new ArrayList<Rational>();
		List<Rational> nus = new ArrayList<Rational>();
		stateInit.putAll(this.m_StateInit);
		stateInit.putAll(other.m_StateInit);
		stateHonda.putAll(this.m_StateHonda);
		stateHonda.putAll(other.m_StateHonda);
		rays.addAll(this.m_Rays);
		rays.addAll(other.m_Rays);
		lambdas.addAll(this.m_Lambdas);
		lambdas.addAll(other.m_Lambdas);
		nus.addAll(this.m_Nus);
		nus.add(Rational.ZERO); // add 0 because the length of nus has to be #rays-1
		nus.addAll(other.m_Nus);
		return new NonTerminationArgument(stateInit, stateHonda, rays, lambdas, nus);
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
	 * @return the number of rays
	 */
	public int getNumberOfRays() {
		return m_Rays.size();
	}
	
	/**
	 * @return the rays of the loop's transition polyhedron 
	 */
	public List<Map<RankVar, Rational>> getRays() {
		// Make unmodifiable view
		List<Map<RankVar, Rational>> rays =
				new ArrayList<Map<RankVar, Rational>>();
		for (Map<RankVar, Rational> ray : m_Rays) {
			rays.add(Collections.unmodifiableMap(ray));
		}
		return Collections.unmodifiableList(rays);
	}
	
	/**
	 * @return the multiplicative factor lambda
	 */
	public List<Rational> getLambdas() {
		return Collections.unmodifiableList(m_Lambdas);
	}
	
	/**
	 * @return the nilpotent factors nu
	 */
	public List<Rational> getNus() {
		return Collections.unmodifiableList(m_Nus);
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
	public static List<Map<Expression, Rational>> rank2Boogie(
			Term2Expression term2expression,
			List<Map<RankVar, Rational>> states) {
		List<Map<Expression, Rational>> result =
				new ArrayList<Map<Expression, Rational>>(states.size());
		Map<Term, Expression> rankVar2Expression =
				new HashMap<Term, Expression>();
		for (Map<RankVar, Rational> state : states) {
			Map<Expression, Rational> expression2rational =
					new LinkedHashMap<Expression, Rational>();
			for (Map.Entry<RankVar, Rational> entry : state.entrySet()) {
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
			result.add(expression2rational);
		}
		return result;
	}
	
	/**
	 * Translate a RankVar into a (Boogie) Expression. The Expression is the
	 * (unique) Expression that represents the definition of the RankVar.
	 */
	private static Expression rankVar2Expression(RankVar rv, 
			Term2Expression term2expression) {
		return term2expression.translate(rv.getDefinition());
	}
	
	public String toString() {
		StringBuilder sb = new StringBuilder();
		sb.append("Non-Termination argument consisting of:\n");
		sb.append("Initial state: ");
		sb.append(m_StateInit);
		sb.append("\nHonda state: ");
		sb.append(m_StateHonda);
		sb.append("\nRays: ");
		sb.append(m_Rays);
		sb.append("\nLambdas: ");
		sb.append(m_Lambdas);
		sb.append("\nNus: ");
		sb.append(m_Nus);
		return sb.toString();
	}
}
