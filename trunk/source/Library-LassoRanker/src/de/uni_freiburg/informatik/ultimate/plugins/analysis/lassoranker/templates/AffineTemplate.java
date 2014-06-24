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
import de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.rankingfunctions.LinearRankingFunction;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.rankingfunctions.RankingFunction;


/**
 * The affine template finds an affine-linear ranking function.
 * 
 * Template:
 * <pre>δ > 0 /\ f(x) > 0 /\ f(x') < f(x) - δ</pre>
 * 
 * @author Jan Leike
 */
public class AffineTemplate extends RankingFunctionTemplate {
	
	private static final String s_name_delta = "delta";
	private static final String s_name_function = "rank";
	
	private Term m_delta;
	private AffineFunctionGenerator m_fgen;
	
	@Override
	protected void init_template() {
		m_delta = newDelta(s_name_delta);
		m_fgen = new AffineFunctionGenerator(m_script, m_variables,
				s_name_function);
	}
	
	@Override
	public String getName() {
		return "affine";
	}
	
	@Override
	public String toString() {
		return "Affine template:\n"
			+ "   delta > 0\n/\\ f(x) > 0\n/\\ f(x) > f(x') + delta";
	}
	
	@Override
	public List<List<LinearInequality>> getConstraints(
			Map<RankVar, Term> inVars, Map<RankVar, Term> outVars) {
		checkInitialized();
		List<List<LinearInequality>> conjunction =
				new ArrayList<List<LinearInequality>>();
		
		// f(x) > 0
		{
			LinearInequality li = m_fgen.generate(inVars);
			li.setStrict(true);
			li.needs_motzkin_coefficient = false;
			conjunction.add(Collections.singletonList(li));
		}
		
		// f(x') < f(x) - delta
		{
			LinearInequality li = m_fgen.generate(inVars);
			LinearInequality li2 = m_fgen.generate(outVars);
			li2.negate();
			li.add(li2);
			AffineTerm a = new AffineTerm(m_delta, Rational.MONE);
			li.add(a);
			li.setStrict(true);
			li.needs_motzkin_coefficient = false;
			conjunction.add(Collections.singletonList(li));
		}
		
		// delta > 0 is assured by RankingFunctionTemplate.newDelta
		return conjunction;
	}

	@Override
	public Collection<Term> getVariables() {
		Collection<Term> list = m_fgen.getVariables();
		list.add(m_delta);
		return list;
	}

	@Override
	public RankingFunction extractRankingFunction(Map<Term, Rational> val)
			throws SMTLIBException {
		AffineFunction f = m_fgen.extractAffineFunction(val);
		return new LinearRankingFunction(f);
	}
	
	@Override
	public List<String> getAnnotations() {
		List<String> annotations = new ArrayList<String>();
		annotations.add("rank bounded");
		annotations.add("rank decreasing");
		return annotations;
	}
	
	@Override
	public int getDegree() {
		return 0;
	}
}