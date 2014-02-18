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
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.AffineFunction;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.AffineFunctionGenerator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.AffineTerm;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.LinearInequality;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.rankingfunctions.NestedRankingFunction;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.rankingfunctions.RankingFunction;


/**
 * The nested template finds ranking functions that decrease each iteration
 * by at least the negated value of another function that is also decreasing.
 * 
 * This seems to be a special case of the Polyranking principle introduced
 * by Bradley, Sipma and Manna. We still have to investigate the exact relation. 
 * 
 * <pre>
 *    δ > 0
 * /\ ( f_0(x) > 0 )
 * /\ ( /\_i f_i(x') < f_i(x) + f_{i+1}(x) )
 * /\ ( f_n(x') < f_n(x) - δ)
 * </pre>
 * 
 * @author Matthias Heizmann
 */
public class NestedTemplate extends RankingFunctionTemplate {
	
	public final int m_Size;
	
	private static final String s_name_delta = "delta";
	private static final String s_name_function = "rank";
	
	private Term m_delta;
	private AffineFunctionGenerator[] m_fgens;
	
	/**
	 * @param functions number of linear functions in the nested template
	 */
	public NestedTemplate(int functions) {
		assert(functions > 0);
		m_Size = functions;
		m_fgens = new AffineFunctionGenerator[m_Size];
	}
	
	@Override
	public void init(Script script, Collection<BoogieVar> vars,
			boolean linear) {
		super.init(script, vars, linear);
		m_delta = RankingFunctionTemplate.newDelta(script, s_name_delta);
		for (int i = 0; i < m_Size; ++i) {
			m_fgens[i] = new AffineFunctionGenerator(script, vars,
					s_name_function + i);
		}
	}
	
	@Override
	public String getName() {
		return m_Size + "-nested";
	}
	
	@Override
	public String toString() {
		StringBuilder sb = new StringBuilder();
		sb.append(m_Size);
		sb.append("-nested template:");
		sb.append("\n");
		sb.append("   ");
		sb.append("delta > 0");
		sb.append("\n");
		sb.append("/\\ f_0(x) > 0");
		sb.append("\n");
		for (int i = 0; i < m_Size-1; ++i) {
			sb.append("/\\ f_" + i + "(x') < f_" + i + "(x) + f_" + (i+1) + "(x)");
			sb.append("\n");
		}
		int n = m_Size-1;
		sb.append("/\\ f_" + n + "(x') < f_" + n + "(x) - delta");
		return sb.toString();
	}
	
	@Override
	public List<List<LinearInequality>> constraints(
			Map<BoogieVar, TermVariable> inVars,
			Map<BoogieVar, TermVariable> outVars) {
		checkInitialized();
		List<List<LinearInequality>> conjunction =
				new ArrayList<List<LinearInequality>>();
		
		// f_0(x) > 0
		List<LinearInequality> disjunction;
		{
			LinearInequality li = m_fgens[0].generate(inVars);
			li.setStrict(true);
			li.needs_motzkin_coefficient = false;
			disjunction = Collections.singletonList(li);
		}
		conjunction.add(disjunction);
		
		// /\_i f_i(x') < f_i(x) - δ_i + f_{i+1}(x)
		for (int i = 0; i < m_Size-1; ++i) {
			disjunction = new ArrayList<LinearInequality>();
			LinearInequality li = m_fgens[i].generate(inVars);
			LinearInequality li2 = m_fgens[i].generate(outVars);
			li2.negate();
			li.add(li2);
			LinearInequality li3 = m_fgens[i+1].generate(inVars);
			li.add(li3);
			li.setStrict(true);
			li.needs_motzkin_coefficient = false;
			disjunction = Collections.singletonList(li);
			conjunction.add(disjunction);
		}
		// f_n(x') < f_n(x) - δ_n
		{
			disjunction = new ArrayList<LinearInequality>();
			LinearInequality li = m_fgens[m_Size-1].generate(inVars);
			LinearInequality li2 = m_fgens[m_Size-1].generate(outVars);
			li2.negate();
			li.add(li2);
			AffineTerm a = new AffineTerm(m_delta, Rational.MONE);
			li.add(a);
			li.setStrict(true);
			li.needs_motzkin_coefficient = false;
			disjunction = Collections.singletonList(li);
			conjunction.add(disjunction);
		}
		
		// delta_i > 0 is assured by RankingFunctionTemplate.newDelta
		return conjunction;
	}

	@Override
	public Collection<Term> getVariables() {
		Collection<Term> list = new ArrayList<Term>();
		list.add(m_delta);
		for (int i = 0; i < m_Size; ++i) {
			list.addAll(m_fgens[i].getVariables());
		}
		return list;
	}

	@Override
	public RankingFunction extractRankingFunction(Map<Term, Rational> val)
			throws SMTLIBException {
		List<AffineFunction> fs = new ArrayList<AffineFunction>();
		for (int i = 0; i < m_Size; ++i) {
			AffineFunction f = m_fgens[i].extractAffineFunction(val);
			fs.add(f);
		}
		return new NestedRankingFunction(fs);
	}
	
	@Override
	public List<String> getAnnotations() {
		List<String> annotations = new ArrayList<String>();
		annotations.add("rank f_0 is bounded");
		for (int i = 0; i < m_Size-1; ++i) {
			annotations.add("rank f_" + i + " is decreasing by at least -f_" + i+1);
		}
		annotations.add("rank f_" + (m_Size-1) + " is decreasing");
		return annotations;
	}
	
	@Override
	public int getDegree() {
		assert(m_Size > 0);
		return 0;
	}
}