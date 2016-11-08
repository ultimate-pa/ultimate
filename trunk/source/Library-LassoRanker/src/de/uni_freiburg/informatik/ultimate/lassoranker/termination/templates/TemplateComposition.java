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
package de.uni_freiburg.informatik.ultimate.lassoranker.termination.templates;

import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.lassoranker.LinearInequality;
import de.uni_freiburg.informatik.ultimate.lassoranker.LinearInequality.PossibleMotzkinCoefficients;


/**
 * 
 * Contains a bunch of static methods that are useful for template composition
 * 
 * @author Jan Leike
 */
public final class TemplateComposition {
	/**
	 * Build a CNF out of a /\ \/ /\ \/ -formula of linear inequalities
	 * using the following rule:
	 * 
	 * <pre>
	 * /\_{i ∈ I} \/_{j ∈ J_i} /\_{k ∈ K_{i,j}} \/_{l ∈ L_{i,j,k}} T(i, j, k, l)
	 * = /\_{i ∈ I} /\_{f ∈ ⨂_{j ∈ J_i} K_{i,j}} \/_{j ∈ J_i} \/_{l ∈ L_{i,j,f(j)}} T(i,j,f(j),l)
	 * </pre>
	 * 
	 * @return a CNF
	 */
	static<T> List<List<T>> distribute(
			List<List<List<List<T>>>> constraints) {
		final List<List<T>> conjunction =
				new ArrayList<List<T>>();
		for (final List<List<List<T>>> i : constraints) {
			final int[] f = new int[i.size()];
			for (int j = 0; j < f.length; ++j) {
				assert !i.get(j).isEmpty();
				f[j] = 0;
			}
			while (true) {
				final List<T> disjuction =
						new ArrayList<T>();
				for (int j = 0; j < f.length; ++j) {
					disjuction.addAll(i.get(j).get(f[j]));
				}
				
				// advance counter
				int j = 0;
				while (j < f.length) {
					++f[j];
					if (f[j] >= i.get(j).size()) {
						f[j] = 0;
						++j;
					} else {
						break;
					}
				}
				conjunction.add(disjuction);
				if (j == f.length) {
					break;
				}
			}
		}
		return conjunction;
	}
	

	/**
	 * Reset all possible Motzkin coefficients to ANYTHING
	 * @param constraints the constraints
	 */
	static void resetMotzkin(List<List<LinearInequality>> constraints) {
		for (final List<LinearInequality> disjunction : constraints) {
			for (final LinearInequality li : disjunction) {
				li.mMotzkinCoefficient = PossibleMotzkinCoefficients.ANYTHING;
			}
//			if (sRedAtoms && disjunction.size() > 0) {
//				disjunction.get(0).motzkin_coefficient =
//					PossibleMotzkinCoefficients.ZERO_AND_ONE;
//			}
		}
	}
	
	/**
	 * Calculate the degree from CNF constraints
	 */
	static int computeDegree(List<List<LinearInequality>> constraints) {
		int degree = 0;
		for (final List<LinearInequality> disjunction : constraints) {
			for (final LinearInequality li : disjunction) {
				if (!li.mMotzkinCoefficient.isFixed()) {
					++degree;
				}
			}
		}
		return degree;
	}
}
