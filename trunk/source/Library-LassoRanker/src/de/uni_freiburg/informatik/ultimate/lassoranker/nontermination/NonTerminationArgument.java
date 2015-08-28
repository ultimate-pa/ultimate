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
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.lassoranker.variables.RankVar;
import de.uni_freiburg.informatik.ultimate.logic.Rational;


/**
 * Represents a non-termination argument for a lasso program in form of an
 * infinite execution.
 * 
 * It is composed of
 * <ul>
 * <li> an initial state at the begin of the lasso,
 * <li> a state at first visit of the honda,
 * <li> a list of generalized eigenvectors of the loop's transition polyhedron,
 * <li> a list of eigenvalues lambda, and
 * <li< a list of nilpotent components mu.
 * </ul>
 * 
 * The infinite execution described by this nontermination argument is
 * 
 * <pre>
 * state_init,
 * state_honda,
 * state_honda + gev_1 + ... + gev_n,
 * state_honda + (1 + lambda_1) gev_1 + (1 + lambda_2 + mu_1) gev_2 + ... + (1 + lambda_n + nu_(n-1)) gev_n,
 * ...
 * </pre>
 * 
 * The general form is x + Y*(sum_i J^i)*1 where
 * <ul>
 * <li> x is the initial state
 * <li> Y is a matrix with the generalized eigenvectors as columns
 * <li> J is a matrix with the eigenvalues lambda_i on the diagonal and
 *      the nilpotent components mu_i on the upper subdiagonal
 * <li> 1 is a column vector of ones
 * </ul>
 * 
 * @author Jan Leike
 */
public class NonTerminationArgument implements Serializable {
	private static final long serialVersionUID = 4606815082909883553L;
	
	private final Map<RankVar, Rational> m_StateInit;
	private final Map<RankVar, Rational> m_StateHonda;
	private final List<Map<RankVar, Rational>> m_GEVs;
	private final List<Rational> m_Lambdas;
	private final List<Rational> m_Nus;
	
	/**
	 * Construct a non-termination argument
	 * 
	 * @param state_init initial state
	 * @param state_honda state at the lasso's honda
	 * @param gevs generalized eigenvalues
	 * @param lambdas eigenvectors
	 * @param nus nilpotent components
	 */
	public NonTerminationArgument(Map<RankVar, Rational> state_init,
			Map<RankVar, Rational> state_honda,
			List<Map<RankVar, Rational>> gevs,
			List<Rational> lambdas,
			List<Rational> nus) {
		assert(state_init != null);
		m_StateInit = state_init;
		assert(state_honda != null);
		m_StateHonda = state_honda;
		assert(gevs != null);
		m_GEVs = gevs;
		assert(lambdas != null);
		m_Lambdas = lambdas;
		assert(nus != null);
		m_Nus = nus;
		assert m_GEVs.size() == lambdas.size();
		assert m_GEVs.size() == nus.size() + 1;
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
		List<Map<RankVar, Rational>> gevs =
				new ArrayList<Map<RankVar, Rational>>();
		List<Rational> lambdas = new ArrayList<Rational>();
		List<Rational> nus = new ArrayList<Rational>();
		stateInit.putAll(this.m_StateInit);
		stateInit.putAll(other.m_StateInit);
		stateHonda.putAll(this.m_StateHonda);
		stateHonda.putAll(other.m_StateHonda);
		gevs.addAll(this.m_GEVs);
		gevs.addAll(other.m_GEVs);
		lambdas.addAll(this.m_Lambdas);
		lambdas.addAll(other.m_Lambdas);
		nus.addAll(this.m_Nus);
		nus.add(Rational.ZERO); // add 0 because the length of nus has to be #gevs-1
		nus.addAll(other.m_Nus);
		return new NonTerminationArgument(stateInit, stateHonda, gevs, lambdas, nus);
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
	 * @return the number of generalized eigenvectors
	 */
	public int getNumberOfGEVs() {
		return m_GEVs.size();
	}
	
	/**
	 * @return the generalized eigenvectors
	 */
	public List<Map<RankVar, Rational>> getGEVs() {
		// Make unmodifiable view
		List<Map<RankVar, Rational>> gevs =
				new ArrayList<Map<RankVar, Rational>>();
		for (Map<RankVar, Rational> gev : m_GEVs) {
			gevs.add(Collections.unmodifiableMap(gev));
		}
		return Collections.unmodifiableList(gevs);
	}
	
	/**
	 * @return the eigenvalue lambda
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
	
	
	public String toString() {
		StringBuilder sb = new StringBuilder();
		sb.append("Non-Termination argument consisting of:\n");
		sb.append("Initial state: ");
		sb.append(m_StateInit);
		sb.append("\nHonda state: ");
		sb.append(m_StateHonda);
		sb.append("\nGeneralized eigenvectors: ");
		sb.append(m_GEVs);
		sb.append("\nLambdas: ");
		sb.append(m_Lambdas);
		sb.append("\nNus: ");
		sb.append(m_Nus);
		return sb.toString();
	}
}
