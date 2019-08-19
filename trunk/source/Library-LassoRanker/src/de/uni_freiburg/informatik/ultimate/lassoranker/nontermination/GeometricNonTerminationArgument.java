/*
 * Copyright (C) 2014-2015 Jan Leike (leike@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 University of Freiburg
 *
 * This file is part of the ULTIMATE LassoRanker Library.
 *
 * The ULTIMATE LassoRanker Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE LassoRanker Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE LassoRanker Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE LassoRanker Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE LassoRanker Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lassoranker.nontermination;

import java.io.Serializable;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.logic.Rational;

/**
 * Represents a non-termination argument for a lasso program in form of an infinite execution.
 *
 * It is composed of
 * <ul>
 * <li>an initial state at the begin of the lasso,
 * <li>a state at first visit of the honda,
 * <li>a list of generalized eigenvectors of the loop's transition polyhedron,
 * <li>a list of eigenvalues lambda, and <li< a list of nilpotent components mu.
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
 * The general form is x + Y*(sumi J^i)*1 where
 * <ul>
 * <li>x is the initial state
 * <li>Y is a matrix with the generalized eigenvectors as columns
 * <li>J is a matrix with the eigenvalues lambda_i on the diagonal and the nilpotent components mu_i on the upper
 * subdiagonal
 * <li>1 is a column vector of ones
 * </ul>
 *
 * @author Jan Leike
 */
public class GeometricNonTerminationArgument extends NonTerminationArgument implements Serializable {
	private static final long serialVersionUID = 4606815082909883553L;

	private final Map<IProgramVar, Rational> mStateInit;
	private final Map<IProgramVar, Rational> mStateHonda;
	private final List<Map<IProgramVar, Rational>> mGEVs;
	private final List<Rational> mLambdas;
	private final List<Rational> mNus;

	/**
	 * Construct a non-termination argument
	 *
	 * @param state_init
	 *            initial state
	 * @param state_honda
	 *            state at the lasso's honda
	 * @param gevs
	 *            generalized eigenvalues
	 * @param lambdas
	 *            eigenvectors
	 * @param nus
	 *            nilpotent components
	 */
	public GeometricNonTerminationArgument(final Map<IProgramVar, Rational> state_init,
			final Map<IProgramVar, Rational> state_honda, final List<Map<IProgramVar, Rational>> gevs,
			final List<Rational> lambdas, final List<Rational> nus) {
		assert (state_init != null);
		mStateInit = state_init;
		assert (state_honda != null);
		mStateHonda = state_honda;
		assert (gevs != null);
		mGEVs = gevs;
		assert (lambdas != null);
		mLambdas = lambdas;
		assert (nus != null);
		mNus = nus;
		assert mGEVs.size() == lambdas.size();
		assert mGEVs.size() == nus.size() + 1 || mGEVs.isEmpty();
	}

	/**
	 * Join the infinite execution of this nontermination argument with another nontermination argument. Variables that
	 * occur in both nontermination arguments but be assigned to the same values.
	 *
	 * This method is used to combine separate arguments that are found after lasso partitioning.
	 */
	public GeometricNonTerminationArgument join(final GeometricNonTerminationArgument other) {
		// Check for compatibility
		for (final IProgramVar rankVar : mStateInit.keySet()) {
			if (other.mStateInit.containsKey(rankVar)) {
				assert mStateInit.get(rankVar).equals(other.mStateInit.get(rankVar));
			}
		}
		for (final IProgramVar rankVar : mStateHonda.keySet()) {
			if (other.mStateHonda.containsKey(rankVar)) {
				assert mStateHonda.get(rankVar).equals(other.mStateHonda.get(rankVar));
			}
		}

		final Map<IProgramVar, Rational> stateInit = new HashMap<>();
		final Map<IProgramVar, Rational> stateHonda = new HashMap<>();
		final List<Map<IProgramVar, Rational>> gevs = new ArrayList<>();
		final List<Rational> lambdas = new ArrayList<>();
		final List<Rational> nus = new ArrayList<>();
		stateInit.putAll(mStateInit);
		stateInit.putAll(other.mStateInit);
		stateHonda.putAll(mStateHonda);
		stateHonda.putAll(other.mStateHonda);
		gevs.addAll(mGEVs);
		gevs.addAll(other.mGEVs);
		lambdas.addAll(mLambdas);
		lambdas.addAll(other.mLambdas);
		nus.addAll(mNus);
		if (!mGEVs.isEmpty() && !other.mGEVs.isEmpty()) {
			nus.add(Rational.ZERO); // add 0 because the length of nus has to be #gevs-1
		}
		nus.addAll(other.mNus);
		return new GeometricNonTerminationArgument(stateInit, stateHonda, gevs, lambdas, nus);
	}

	/**
	 * @return the initial state
	 */
	public Map<IProgramVar, Rational> getStateInit() {
		return Collections.unmodifiableMap(mStateInit);
	}

	/**
	 * @return the state at the lasso's honda
	 */
	public Map<IProgramVar, Rational> getStateHonda() {
		return Collections.unmodifiableMap(mStateHonda);
	}

	/**
	 * @return the number of generalized eigenvectors
	 */
	public int getNumberOfGEVs() {
		return mGEVs.size();
	}

	/**
	 * @return the generalized eigenvectors
	 */
	public List<Map<IProgramVar, Rational>> getGEVs() {
		// Make unmodifiable view
		final List<Map<IProgramVar, Rational>> gevs = new ArrayList<>();
		for (final Map<IProgramVar, Rational> gev : mGEVs) {
			gevs.add(Collections.unmodifiableMap(gev));
		}
		return Collections.unmodifiableList(gevs);
	}

	/**
	 * @return the eigenvalue lambda
	 */
	public List<Rational> getLambdas() {
		return Collections.unmodifiableList(mLambdas);
	}

	/**
	 * @return the nilpotent factors nu
	 */
	public List<Rational> getNus() {
		return Collections.unmodifiableList(mNus);
	}

	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();
		sb.append("Non-Termination argument consisting of: ");
		sb.append("Initial state: ");
		sb.append(mStateInit);
		sb.append(" Honda state: ");
		sb.append(mStateHonda);
		sb.append(" Generalized eigenvectors: ");
		sb.append(mGEVs);
		sb.append(" Lambdas: ");
		sb.append(mLambdas);
		sb.append(" Nus: ");
		sb.append(mNus);
		return sb.toString();
	}
}
