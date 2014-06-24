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
import de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.rankingfunctions.ParallelRankingFunction;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.rankingfunctions.RankingFunction;


/**
 * The parallel template finds ranking functions that consist of multiple
 * linear ranking functions that decrease in any order.
 * 
 * On the ordinals, a parallel ranking function represents the addition of
 * two (linear) ranking functions. It is probably only really useful as
 * a composition of two (or more) other templates.
 * 
 * Warning: the size of the constraints is _exponential_ in the number of
 *          parallel ranking functions
 * 
 * TODO: this template does not have the correct degree!
 * 
 * Template:
 * <pre>
 * /\_i δ_i > 0
 * /\_i f_i(x') <= f_i(x)
 * /\ ( \/_i (f_i(x) > 0 /\ f_i(x') < f_i(x) - δ_i ))
 * </pre>
 * 
 * @author Jan Leike
 */
public class ParallelTemplate extends RankingFunctionTemplate {
	
	public final int size;
	
	private static final String s_name_delta = "delta";
	private static final String s_name_function = "rank";
	
	private Term[] m_deltas;
	private AffineFunctionGenerator[] m_fgens;
	
	/**
	 * @param num_functions number of parallel ranking functions
	 */
	public ParallelTemplate(int num_functions) {
		assert(num_functions > 0);
		assert(num_functions <= 30); // reasonable upper size bound
		                             // until the singularity
		assert((1 << num_functions) > 0); // remember, this is exponential
		size = num_functions;
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
		return size + "-parallel";
	}
	
	@Override
	public String toString() {
		StringBuilder sb = new StringBuilder();
		sb.append(size);
		sb.append("-parallel template:\n   ");
		for (int i = 0; i < size; ++i) {
			if (i > 0) {
				sb.append("/\\ ");
			}
			sb.append("delta_" + i + " > 0\n");
		}
		for (int i = 0; i < size; ++i) {
			sb.append("/\\ f_" + i + "(x') <= f_" + i + "(x)\n");
		}
		for (int k = 0; k < (1 << size); ++k) {
			sb.append("/\\ ( ");
			for (int i = 0; i < size; ++i) {
				if ((k & (1 << i)) == 0) {
					sb.append("f_" + i + " > 0");
				} else {
					sb.append("f_" + i + "(x') < f_" + i + "(x) - delta_" + i);
				}
				if (i < size - 1) {
					sb.append(" \\/ ");
				}
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
		
		// /\_i f_i(x') <= f_i(x)
		for (int i = 0; i < size; ++i) {
			LinearInequality li = m_fgens[i].generate(inVars);
			LinearInequality li2 = m_fgens[i].generate(outVars);
			li2.negate();
			li.add(li2);
			li.needs_motzkin_coefficient = false;
			conjunction.add(Collections.singletonList(li));
		}
		
		// /\ ( \/_i (f_i(x) > 0 /\ f_i(x') < f_i(x) - δ_i ))
		for (int k = 0; k < (1 << size); ++k) {
			// This is done in conjunctive normal form
			List<LinearInequality> disjunction =
					new ArrayList<LinearInequality>();
			for (int i = 0; i < size; ++i) {
				if ((k & (1 << i)) == 0) {
					// f_i(x) > 0
					LinearInequality li = m_fgens[i].generate(inVars);
					li.setStrict(true);
					li.needs_motzkin_coefficient = i > 0;
					disjunction.add(li);
				} else {
					// f_i(x') < f_i(x) - δ_i
					LinearInequality li = m_fgens[i].generate(inVars);
					LinearInequality li2 = m_fgens[i].generate(outVars);
					li2.negate();
					li.add(li2);
					AffineTerm a = new AffineTerm(m_deltas[i], Rational.MONE);
					li.add(a);
					li.setStrict(true);
					li.needs_motzkin_coefficient = i > 0;
					disjunction.add(li);
				}
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
		return new ParallelRankingFunction(fs);
	}
	
	@Override
	public List<String> getAnnotations() {
		List<String> annotations = new ArrayList<String>();
		for (int i = 0; i < size; ++i) {
			annotations.add("rank f" + i + " is not increasing");
		}
		for (int k = 0; k < (1 << size); ++k) {
			StringBuilder sb = new StringBuilder();
			for (int i = 0; i < size; ++i) {
				if (i > 0) {
					sb.append(" or ");
				}
				if ((k & (1 << i)) == 0) {
					sb.append("rank f" + i + " is positive");
				} else {
					sb.append("rank f" + i + " is decreasing");
				}
			}
			annotations.add(sb.toString());
		}
		return annotations;
	}
	
	@Override
	public int getDegree() {
		assert(size > 0);
		return (1 << size)*(size - 1);
	}
}