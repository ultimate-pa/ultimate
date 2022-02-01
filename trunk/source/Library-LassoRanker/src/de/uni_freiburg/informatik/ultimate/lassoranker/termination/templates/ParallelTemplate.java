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
import de.uni_freiburg.informatik.ultimate.lassoranker.termination.rankingfunctions.ParallelRankingFunction;
import de.uni_freiburg.informatik.ultimate.lassoranker.termination.rankingfunctions.RankingFunction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;


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
public class ParallelTemplate extends RankingTemplate {
	
	public final int size;
	
	private static final String s_name_delta = "delta";
	private static final String s_name_function = "rank";
	
	private final Term[] mdeltas;
	private final AffineFunctionGenerator[] mfgens;
	
	/**
	 * @param numfunctions number of parallel ranking functions
	 */
	public ParallelTemplate(final int numfunctions) {
		assert(numfunctions > 1);
		assert(numfunctions <= 30); // reasonable upper size bound
		                             // until the singularity arrives
		assert((1 << numfunctions) > 0); // remember, this template's size is exponential!
		size = numfunctions;
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
		return size + "-parallel";
	}
	
	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();
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
			final Map<IProgramVar, TermVariable> inVars, final Map<IProgramVar, TermVariable> outVars) {
		checkInitialized();
		final List<List<LinearInequality>> conjunction =
				new ArrayList<List<LinearInequality>>();
		
		// /\_i f_i(x') <= f_i(x)
		for (int i = 0; i < size; ++i) {
			final LinearInequality li = mfgens[i].generate(inVars);
			final LinearInequality li2 = mfgens[i].generate(outVars);
			li2.negate();
			li.add(li2);
			li.mMotzkinCoefficient = RED_ATOMS ?
					PossibleMotzkinCoefficients.ONE
					: PossibleMotzkinCoefficients.ANYTHING;
			conjunction.add(Collections.singletonList(li));
		}
		
		// /\ ( \/_i (f_i(x) > 0 /\ f_i(x') < f_i(x) - δ_i ))
		for (int k = 0; k < (1 << size); ++k) {
			// This is done in conjunctive normal form
			final List<LinearInequality> disjunction =
					new ArrayList<LinearInequality>();
			for (int i = 0; i < size; ++i) {
				if ((k & (1 << i)) == 0) {
					// f_i(x) > 0
					final LinearInequality li = mfgens[i].generate(inVars);
					li.setStrict(true);
					li.mMotzkinCoefficient = RED_ATOMS && i == 0 ?
							PossibleMotzkinCoefficients.ZERO_AND_ONE
							: PossibleMotzkinCoefficients.ANYTHING;
					disjunction.add(li);
				} else {
					// f_i(x') < f_i(x) - δ_i
					final LinearInequality li = mfgens[i].generate(inVars);
					final LinearInequality li2 = mfgens[i].generate(outVars);
					li2.negate();
					li.add(li2);
					final AffineTerm a = new AffineTerm(mdeltas[i], Rational.MONE);
					li.add(a);
					li.setStrict(true);
					li.mMotzkinCoefficient = RED_ATOMS && i == 0 ?
							PossibleMotzkinCoefficients.ZERO_AND_ONE
							: PossibleMotzkinCoefficients.ANYTHING;
					disjunction.add(li);
				}
			}
			conjunction.add(disjunction);
		}
		
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
		final AffineFunction[] fs = new AffineFunction[size];
		for (int i = 0; i < size; ++i) {
			fs[i] = mfgens[i].extractAffineFunction(val);
		}
		return new ParallelRankingFunction(fs);
	}
	
	@Override
	public List<String> getAnnotations() {
		final List<String> annotations = new ArrayList<String>();
		for (int i = 0; i < size; ++i) {
			annotations.add("rank f" + i + " is not increasing");
		}
		for (int k = 0; k < (1 << size); ++k) {
			final StringBuilder sb = new StringBuilder();
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
		return (1 << size)*(size - 1); // TODO: find some blue atoms
	}
}
