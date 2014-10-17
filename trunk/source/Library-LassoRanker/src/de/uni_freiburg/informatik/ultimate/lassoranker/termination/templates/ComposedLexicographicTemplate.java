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
package de.uni_freiburg.informatik.ultimate.lassoranker.termination.templates;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.lassoranker.LinearInequality;
import de.uni_freiburg.informatik.ultimate.lassoranker.LinearInequality.PossibleMotzkinCoefficients;
import de.uni_freiburg.informatik.ultimate.lassoranker.termination.rankingfunctions.LexicographicRankingFunction;
import de.uni_freiburg.informatik.ultimate.lassoranker.termination.rankingfunctions.RankingFunction;
import de.uni_freiburg.informatik.ultimate.lassoranker.variables.RankVar;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Term;


/**
 * A composed lexicographic template is a ranking template that
 * corresponds to a lexicographic ranking function where
 * each entry is a ranking function from a composable template.
 * 
 * @author Jan Leike
 */
public class ComposedLexicographicTemplate extends ComposableTemplate {
	
	ComposableTemplate[] m_Parts;
	
	/**
	 * Construct a new ComposedLexicographicTemplate
	 * 
	 * @param parts the ranking templates that are used as lexicographic entries
	 */
	public ComposedLexicographicTemplate(ComposableTemplate[] parts) {
		assert(parts.length >= 1);
		m_Parts = parts;
	}
	
	@Override
	protected void _init() {
		for (ComposableTemplate t : m_Parts) {
			t.init(m_tas);
		}
	}

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
		List<List<T>> conjunction =
				new ArrayList<List<T>>();
		for (List<List<List<T>>> i : constraints) {
			int[] f = new int[i.size()];
			for (int j = 0; j < f.length; ++j) {
				assert !i.get(j).isEmpty();
				f[j] = 0;
			}
			while (true) {
				List<T> disjuction =
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
		for (List<LinearInequality> disjunction : constraints) {
			for (LinearInequality li : disjunction) {
				li.motzkin_coefficient = PossibleMotzkinCoefficients.ANYTHING;
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
		for (List<LinearInequality> disjunction : constraints) {
			for (LinearInequality li : disjunction) {
				if (!li.motzkin_coefficient.isFixed()) {
					++degree;
				}
			}
		}
		return degree;
	}
	
	@Override
	public String getName() {
		StringBuilder sb = new StringBuilder();
		sb.append("lex(");
		boolean first = true;
		for (ComposableTemplate t : m_Parts) {
			if (!first) {
				sb.append(", ");
			}
			sb.append(t.getName());
			first = false;
		}
		sb.append(")");
		return sb.toString();
	}

	@Override
	public List<List<LinearInequality>> getConstraintsDec(
			Map<RankVar, Term> inVars, Map<RankVar, Term> outVars) {
		List<List<List<List<LinearInequality>>>> constraints =
				new ArrayList<List<List<List<LinearInequality>>>>();
		
		// \/_i T_i^<
		{
			List<List<List<LinearInequality>>> disjunction =
					new ArrayList<List<List<LinearInequality>>>();
			for (ComposableTemplate t : m_Parts) {
				disjunction.add(t.getConstraintsDec(inVars, outVars));
			}
			constraints.add(disjunction);
		}
		
		// /\_{i<k-1} (T_i^≤ \/ \/_{j < i} T_j^<)
		for (int i = 0; i < m_Parts.length - 1; ++i) {
			List<List<List<LinearInequality>>> disjunction =
					new ArrayList<List<List<LinearInequality>>>();
			disjunction.add(m_Parts[i].getConstraintsNonInc(inVars, outVars));
			for (int j = 0; j < i; ++j) {
				disjunction.add(m_Parts[j].getConstraintsDec(inVars, outVars));
			}
			constraints.add(disjunction);
		}
		
		List<List<LinearInequality>> cnf = distribute(constraints);
		resetMotzkin(cnf);
		return cnf;
	}


	@Override
	public List<List<LinearInequality>> getConstraintsNonInc(
			Map<RankVar, Term> inVars, Map<RankVar, Term> outVars) {
		List<List<List<List<LinearInequality>>>> constraints =
				new ArrayList<List<List<List<LinearInequality>>>>();
		// /\_i (T_i^≤ \/ \/_{j < i} T_j^<)
		for (int i = 0; i < m_Parts.length; ++i) {
			List<List<List<LinearInequality>>> disjunction =
					new ArrayList<List<List<LinearInequality>>>();
			disjunction.add(m_Parts[i].getConstraintsNonInc(inVars, outVars));
			for (int j = 0; j < i; ++j) {
				disjunction.add(m_Parts[j].getConstraintsDec(inVars, outVars));
			}
			constraints.add(disjunction);
		}
		
		List<List<LinearInequality>> cnf = distribute(constraints);
		resetMotzkin(cnf);
		return cnf;
	}

	@Override
	public List<List<LinearInequality>> getConstraintsBounded(
			Map<RankVar, Term> inVars, Map<RankVar, Term> outVars) {
		List<List<List<List<LinearInequality>>>> constraints =
				new ArrayList<List<List<List<LinearInequality>>>>();
		
		// /\_i T_i^{>0}
		for (ComposableTemplate t : m_Parts) {
			constraints.add(Collections.singletonList(
					t.getConstraintsBounded(inVars, outVars)));
		}
		
		List<List<LinearInequality>> cnf = distribute(constraints);
		resetMotzkin(cnf);
		return cnf;
	}

	private List<String> blankAnnotations(int size) {
		List<String> annotations = new ArrayList<String>(size);
		for (int i = 0; i < size; ++i) {
			annotations.add("");
		}
		return annotations;
	}

	@Override
	public List<String> getAnnotationsDec() {
		// TODO
		Map<RankVar, Term> empty = Collections.emptyMap();
		return blankAnnotations(getConstraintsDec(empty, empty).size());
	}


	@Override
	public List<String> getAnnotationsNonInc() {
		// TODO
		Map<RankVar, Term> empty = Collections.emptyMap();
		return blankAnnotations(getConstraintsNonInc(empty, empty).size());
	}

	@Override
	public List<String> getAnnotationsBounded() {
		// TODO
		Map<RankVar, Term> empty = Collections.emptyMap();
		return blankAnnotations(getConstraintsBounded(empty, empty).size());
	}
	
	@Override
	public String toString() {
		return ""; // TODO
	}
	
	@Override
	public Collection<Term> getVariables() {
		List<Term> variables = new ArrayList<Term>();
		for (ComposableTemplate t : m_Parts) {
			variables.addAll(t.getVariables());
		}
		return variables;
	}

	@Override
	public int getDegree() {
		Map<RankVar, Term> empty = Collections.emptyMap();
		return computeDegree(getConstraintsBounded(empty, empty))
				+ computeDegree(getConstraintsDec(empty, empty));
	}

	@Override
	public RankingFunction extractRankingFunction(Map<Term, Rational> val)
			throws SMTLIBException {
		RankingFunction[] rfs = new RankingFunction[m_Parts.length];
		for (int i = 0; i < m_Parts.length; ++i) {
			rfs[i] = m_Parts[i].extractRankingFunction(val);
		}
		return new LexicographicRankingFunction(rfs);
	}
}
