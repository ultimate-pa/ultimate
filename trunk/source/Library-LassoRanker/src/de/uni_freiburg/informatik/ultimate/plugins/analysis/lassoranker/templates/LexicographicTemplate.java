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
package de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.templates;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.AffineFunction;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.AffineFunctionGenerator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.AffineTerm;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.LinearInequality;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.RankVar;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.rankingfunctions.LexicographicRankingFunction;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.rankingfunctions.RankingFunction;


/**
 * The lexicographic template finds lexicographic ranking functions where each
 * entry is an affine-linear function.
 * 
 * Template:
 * <pre>
 *    /\_i δ_i > 0
 * /\ /\_i f_i(x) > 0
 * /\ ( /\_(i < k) f_i(x') ≤ f_i(x) \/ \/_(j<i) f_j(x') < f_j(x) - δ_j )
 * /\ ( \/_i f_i(x') < f_i(x) - δ_i )
 * </pre>
 * 
 * @author Jan Leike
 */
public class LexicographicTemplate extends RankingFunctionTemplate {
	
	public final int size;
	
	private static final String s_name_delta = "delta";
	private static final String s_name_function = "rank";
	
	private Term[] m_deltas;
	private AffineFunctionGenerator[] m_fgens;
	
	/**
	 * @param num_functions number of lexicographic components
	 */
	public LexicographicTemplate(int num_lex) {
		assert(num_lex > 0);
		size = num_lex;
		m_deltas = new Term[size];
		m_fgens = new AffineFunctionGenerator[size];
	}
	
	@Override
	protected void init_template() {
		for (int i = 0; i < size; ++i) {
			m_deltas[i] = newDelta(s_name_delta + i);
			m_fgens[i] = new AffineFunctionGenerator(m_script, m_variables,
					s_name_function + i);
		}
	}
	
	@Override
	public String getName() {
		return size + "-lex";
	}
	
	@Override
	public String toString() {
		StringBuilder sb = new StringBuilder();
		sb.append(size);
		sb.append("-lex template:\n   ");
		for (int i = 0; i < size; ++i) {
			sb.append("delta_" + i + " > 0\n/\\ ");
		}
		for (int i = 0; i < size; ++i) {
			sb.append("f_" + i + "(x) > 0\n/\\ ");
		}
		for (int i = 0; i < size - 1; ++i) {
			sb.append("( f_" + i + "(x') <= f_" + i + "(x)");
			for (int j = i - 1; j >= 0; --j) {
				sb.append(" \\/ f_" + j + "(x') < f_" + j + "(x) - delta_" + j);
			}
			sb.append(" )\n/\\ ");
		}
		sb.append("( ");
		for (int i = 0; i < size; ++i) {
			sb.append("f_" + i + "(x') < f_" + i + "(x) - delta_" + i);
			if (i < size - 1) {
				sb.append(" \\/ ");
			}
		}
		sb.append(" )");
		return sb.toString();
	}
	
	@Override
	public List<List<LinearInequality>> getConstraints(
			Map<RankVar, Term> inVars, Map<RankVar, Term> outVars) {
		checkInitialized();
		List<List<LinearInequality>> conjunction =
				new ArrayList<List<LinearInequality>>();
		
		// /\_i f_i(x) > 0
		for (int i = 0; i < size; ++i) {
			LinearInequality li = m_fgens[i].generate(inVars);
			li.setStrict(true);
			li.needs_motzkin_coefficient = false;
			conjunction.add(Collections.singletonList(li));
		}
		
		// /\_(i < k) f_i(x') ≤ f_i(x) \/ \/_(j<i) f_j(x') < f_j(x) - δ_j
		for (int i = 0; i < size - 1; ++i) {
			List<LinearInequality> disjunction =
					new ArrayList<LinearInequality>();
			LinearInequality li = m_fgens[i].generate(inVars);
			LinearInequality li2 = m_fgens[i].generate(outVars);
			li2.negate();
			li.add(li2);
			li.setStrict(false);
			li.needs_motzkin_coefficient = false;
			disjunction.add(li);
			
			for (int j = i - 1; j >= 0; --j) {
				li = m_fgens[j].generate(inVars);
				LinearInequality li3 = m_fgens[j].generate(outVars);
				li3.negate();
				li.add(li3);
				AffineTerm a = new AffineTerm(m_deltas[j], Rational.MONE);
				li.add(a);
				li.setStrict(true);
				li.needs_motzkin_coefficient = !m_linear && j > 0;
				disjunction.add(li);
			}
			conjunction.add(disjunction);
		}
		
		// \/_i f_i(x') < f_i(x) - δ_i
		List<LinearInequality> disjunction = new ArrayList<LinearInequality>();
		for (int i = 0; i < size; ++i) {
			LinearInequality li = m_fgens[i].generate(inVars);
			LinearInequality li2 = m_fgens[i].generate(outVars);
			li2.negate();
			li.add(li2);
			AffineTerm a = new AffineTerm(m_deltas[i], Rational.MONE);
			li.add(a);
			li.setStrict(true);
			li.needs_motzkin_coefficient = !m_linear && i > 0 && i < size - 1;
			disjunction.add(li);
		}
		conjunction.add(disjunction);
		
		// delta_i > 0 is assured by RankingFunctionTemplate.newDelta
		return conjunction;
	}

	@Override
	public Collection<Term> getVariables() {
		Collection<Term> list = new ArrayList<Term>();
		for (int i = 0; i < size; ++i) {
			list.addAll(m_fgens[i].getVariables());
			list.add(m_deltas[i]);
		}
		return list;
	}

	@Override
	public RankingFunction extractRankingFunction(Map<Term, Rational> val)
			throws SMTLIBException {
		AffineFunction[] fs = new AffineFunction[size];
		for (int i = 0; i < size; ++i) {
			fs[i] = m_fgens[i].extractAffineFunction(val);
		}
		return new LexicographicRankingFunction(fs);
	}
	
	@Override
	public List<String> getAnnotations() {
		List<String> annotations = new ArrayList<String>();
		for (int i = 0; i < size; ++i) {
			annotations.add("rank f" + i + " is bounded");
		}
		for (int i = 0; i < size - 1; ++i) {
			annotations.add("rank f" + i + " is not increasing unless "
					+ "a smaller index decreases");
		}
		annotations.add("at least one rank index decreases");
		return annotations;
	}

	@Override
	public int getDegree() {
		assert(size > 0);
		return (size - 1)*(size - 2) / 2;
	}
}