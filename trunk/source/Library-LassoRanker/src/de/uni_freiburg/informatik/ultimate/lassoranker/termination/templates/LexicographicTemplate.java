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
import java.util.Collection;
import java.util.Collections;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.lassoranker.AffineTerm;
import de.uni_freiburg.informatik.ultimate.lassoranker.LinearInequality;
import de.uni_freiburg.informatik.ultimate.lassoranker.LinearInequality.PossibleMotzkinCoefficients;
import de.uni_freiburg.informatik.ultimate.lassoranker.termination.AffineFunction;
import de.uni_freiburg.informatik.ultimate.lassoranker.termination.AffineFunctionGenerator;
import de.uni_freiburg.informatik.ultimate.lassoranker.termination.rankingfunctions.LexicographicRankingFunction;
import de.uni_freiburg.informatik.ultimate.lassoranker.termination.rankingfunctions.LinearRankingFunction;
import de.uni_freiburg.informatik.ultimate.lassoranker.termination.rankingfunctions.RankingFunction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;


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
public class LexicographicTemplate extends RankingTemplate {
	
	public final int size;
	
	private static final String s_name_delta = "delta";
	private static final String s_name_function = "rank";
	
	private final Term[] mdeltas;
	private final AffineFunctionGenerator[] mfgens;
	
	/**
	 * @param numfunctions number of lexicographic components
	 */
	public LexicographicTemplate(final int numlex) {
		assert(numlex > 1);
		size = numlex;
		mdeltas = new Term[size];
		mfgens = new AffineFunctionGenerator[size];
	}
	
	@Override
	protected void init() {
		for (int i = 0; i < size; ++i) {
			mdeltas[i] = newDelta(s_name_delta + i);
			mfgens[i] = new AffineFunctionGenerator(mScript, mVariables,
					s_name_function + i);
		}
	}
	
	@Override
	public String getName() {
		return size + "-lex";
	}
	
	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();
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
			final Map<IProgramVar, TermVariable> inVars, final Map<IProgramVar, TermVariable> outVars) {
		checkInitialized();
		final List<List<LinearInequality>> conjunction =
				new ArrayList<List<LinearInequality>>();
		
		// /\_i f_i(x) > 0
		for (int i = 0; i < size; ++i) {
			final LinearInequality li = mfgens[i].generate(inVars);
			li.setStrict(true);
			li.mMotzkinCoefficient = RED_ATOMS ? PossibleMotzkinCoefficients.ONE
					: PossibleMotzkinCoefficients.ANYTHING;
			conjunction.add(Collections.singletonList(li));
		}
		
		// /\_(i < k) f_i(x') ≤ f_i(x) \/ \/_(j<i) f_j(x') < f_j(x) - δ_j
		for (int i = 0; i < size - 1; ++i) {
			final List<LinearInequality> disjunction =
					new ArrayList<LinearInequality>();
			LinearInequality li = mfgens[i].generate(inVars);
			final LinearInequality li2 = mfgens[i].generate(outVars);
			li2.negate();
			li.add(li2);
			li.setStrict(false);
			li.mMotzkinCoefficient = BLUE_ATOMS ?
					PossibleMotzkinCoefficients.ZERO_AND_ONE
					: PossibleMotzkinCoefficients.ANYTHING;
			disjunction.add(li);
			
			for (int j = i - 1; j >= 0; --j) {
				li = mfgens[j].generate(inVars);
				final LinearInequality li3 = mfgens[j].generate(outVars);
				li3.negate();
				li.add(li3);
				final AffineTerm a = new AffineTerm(mdeltas[j], Rational.MONE);
				li.add(a);
				li.setStrict(true);
				li.mMotzkinCoefficient = RED_ATOMS && j == 0 ?
						PossibleMotzkinCoefficients.ZERO_AND_ONE
						: PossibleMotzkinCoefficients.ANYTHING;
				disjunction.add(li);
			}
			conjunction.add(disjunction);
		}
		
		// \/_i f_i(x') < f_i(x) - δ_i
		final List<LinearInequality> disjunction = new ArrayList<LinearInequality>();
		for (int i = 0; i < size; ++i) {
			final LinearInequality li = mfgens[i].generate(inVars);
			final LinearInequality li2 = mfgens[i].generate(outVars);
			li2.negate();
			li.add(li2);
			final AffineTerm a = new AffineTerm(mdeltas[i], Rational.MONE);
			li.add(a);
			li.setStrict(true);
			li.mMotzkinCoefficient = (RED_ATOMS && i == 0) || (BLUE_ATOMS && i == size - 1) ?
					PossibleMotzkinCoefficients.ZERO_AND_ONE
					: PossibleMotzkinCoefficients.ANYTHING;
			disjunction.add(li);
		}
		conjunction.add(disjunction);
		
		// delta_i > 0 is assured by RankingFunctionTemplate.newDelta
		return conjunction;
	}

	@Override
	public Collection<Term> getCoefficients() {
		final Collection<Term> list = new ArrayList<Term>();
		for (int i = 0; i < size; ++i) {
			list.addAll(mfgens[i].getCoefficients());
			list.add(mdeltas[i]);
		}
		return list;
	}

	@Override
	public RankingFunction extractRankingFunction(final Map<Term, Rational> val)
			throws SMTLIBException {
		final RankingFunction[] rfs = new RankingFunction[size];
		for (int i = 0; i < size; ++i) {
			final AffineFunction af = mfgens[i].extractAffineFunction(val);
			rfs[i] = new LinearRankingFunction(af);
		}
		return new LexicographicRankingFunction(rfs);
	}
	
	@Override
	public List<String> getAnnotations() {
		final List<String> annotations = new ArrayList<String>();
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
		return size*(size - 1) / 2;
	}
}
