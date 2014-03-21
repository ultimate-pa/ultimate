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
package de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker;

import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;


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
public class NonTerminationArgument {
	
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
	 * Translate states with RankVar domains to states with BoogieVar domains.
	 * Boolean are translated to 1 (true) and 0 (false).
	 * @param state a state mapping RankVar's to Rational's
	 * @return a state mapping the corresponding BoogieVar's to Rational's
	 */
	public static Map<BoogieVar, Rational> rank2Boogie(
			Map<RankVar, Rational> state) {
		Map<BoogieVar, Rational> result =
				new LinkedHashMap<BoogieVar, Rational>();
		for (Map.Entry<RankVar, Rational> entry : state.entrySet()) {
			BoogieVar boogieVar = entry.getKey().getAssociatedBoogieVar();
			if (boogieVar == null) {
				// No associated BoogieVar, safe to skip
				continue;
			}
			// Replace boolean BoogieVars
			if (boogieVar.getTermVariable().getSort().getName().equals("Bool")) {
				// value >= 1 means true, which is translated to 1,
				// false is translated to 0.
				Rational value =
						entry.getValue().compareTo(Rational.ONE) == -1 ?
								Rational.ONE : Rational.ZERO;
				result.put(boogieVar, value);
				continue;
			}
			result.put(boogieVar, entry.getValue()); // fallback: do nothing
		}
		return result;
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
