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
import de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.rankingfunctions.MultiphaseRankingFunction;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.rankingfunctions.RankingFunction;


/**
 * The multiphase template finds ranking functions that proceed through a
 * fixed number of phases where each phase is ranked by an affine-linear
 * function.
 * 
 * Template:
 * <pre>
 *    /\_i δ_i > 0
 * /\ ( \/_i f_i(x) > 0 )
 * /\ ( /\_i (f_i(x') < f_i(x) - δ_i \/ \/_(j<i) f_j(x) > 0 )
 * </pre>
 * 
 * @author Jan Leike
 */
public class MultiphaseTemplate extends RankingFunctionTemplate {
	
	public final int size;
	
	private static final String s_name_delta = "delta";
	private static final String s_name_function = "rank";
	
	private Term[] m_deltas;
	private AffineFunctionGenerator[] m_fgens;
	
	/**
	 * @param num_phases number of phases in the multiphase template
	 */
	public MultiphaseTemplate(int num_phases) {
		assert(num_phases > 0);
		size = num_phases;
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
		return size + "-phase";
	}
	
	@Override
	public String toString() {
		StringBuilder sb = new StringBuilder();
		sb.append(size);
		sb.append("-phase template:\n   ");
		for (int i = 0; i < size; ++i) {
			sb.append("delta_" + i + " > 0\n/\\ ");
		}
		sb.append("( ");
		for (int i = 0; i < size; ++i) {
			sb.append("f_" + i + "(x) > 0");
			if (i < size - 1) {
				sb.append(" \\/ ");
			}
		}
		sb.append(" )\n");
		for (int i = 0; i < size; ++i) {
			sb.append("/\\ ( f_" + i + "(x') < f_" + i + "(x) - delta_" + i);
			for (int j = i - 1; j >= 0; --j) {
				sb.append(" \\/ f_" + j + "(x) > 0");
			}
			sb.append(" )\n");
		}
		return sb.toString();
	}
	
	@Override
	public List<List<LinearInequality>> getConstraints(
			Map<RankVar, Term> inVars, Map<RankVar, Term> outVars) {
		checkInitialized();
		List<List<LinearInequality>> conjunction =
				new ArrayList<List<LinearInequality>>();
		
		// \/_i f_i(x) > 0
		List<LinearInequality> disjunction =
				new ArrayList<LinearInequality>();
		for (int i = 0; i < size; ++i) {
			LinearInequality li = m_fgens[i].generate(inVars);
			li.setStrict(true);
			li.needs_motzkin_coefficient = !m_linear && i > 0;
			disjunction.add(li);
		}
		conjunction.add(disjunction);
		
		// /\_i ( f_i(x') < f_i(x) - δ_i \/ \/_(j<i) f_j(x) > 0 )
		for (int i = 0; i < size; ++i) {
			disjunction = new ArrayList<LinearInequality>();
			LinearInequality li = m_fgens[i].generate(inVars);
			LinearInequality li2 = m_fgens[i].generate(outVars);
			li2.negate();
			li.add(li2);
			AffineTerm a = new AffineTerm(m_deltas[i], Rational.MONE);
			li.add(a);
			li.setStrict(true);
			li.needs_motzkin_coefficient = false;
			disjunction.add(li);
			for (int j = i - 1; j >= 0; --j) {
				LinearInequality li3 = m_fgens[j].generate(inVars);
				li3.setStrict(true);
				li3.needs_motzkin_coefficient = !m_linear && j > 0;
				disjunction.add(li3);
			}
			conjunction.add(disjunction);
		}
		
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
		return new MultiphaseRankingFunction(fs);
	}
	
	@Override
	public List<String> getAnnotations() {
		List<String> annotations = new ArrayList<String>();
		annotations.add("at least one rank f_i is bounded");
		for (int i = 0; i < size; ++i) {
			annotations.add("rank f" + i + " is decreasing in phase " + i);
		}
		return annotations;
	}
	
	@Override
	public int getDegree() {
		assert(size > 0);
		return size*(size - 1) / 2;
	}
}