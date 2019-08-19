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
import de.uni_freiburg.informatik.ultimate.lassoranker.termination.rankingfunctions.MultiphaseRankingFunction;
import de.uni_freiburg.informatik.ultimate.lassoranker.termination.rankingfunctions.RankingFunction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;


/**
 * The multiphase template finds ranking functions that proceed through a
 * fixed number of phases where each phase is ranked by an affine-linear
 * function.
 * 
 * Template:
 * <pre>
 *    /\_i δ_i > 0
 * /\ \/_i f_i(x) > 0
 * /\ f_0(x') < f_0(x) - δ_0
 * /\ /\_{i>0} (f_i(x') < f_i(x) - δ_i \/ f_{i-1}(x) > 0)
 * </pre>
 * 
 * @author Jan Leike
 */
public class MultiphaseTemplate extends ComposableTemplate {
	
	public final int size;
	
	private static final String s_name_delta = "delta_";
	private static final String s_name_function = "rank_";
	
	private final Term[] mdeltas;
	private final AffineFunctionGenerator[] mfgens;
	
	/**
	 * @param numphases number of phases in the multiphase template
	 */
	public MultiphaseTemplate(final int numphases) {
		assert(numphases > 1);
		size = numphases;
		mdeltas = new Term[size];
		mfgens = new AffineFunctionGenerator[size];
	}
	
	@Override
	protected void init() {
		for (int i = 0; i < size; ++i) {
			mdeltas[i] = newDelta(s_name_delta + getInstanceNumber() + "_" + i);
			mfgens[i] = new AffineFunctionGenerator(mScript, mVariables,
					s_name_function + getInstanceNumber() + "_" + i);
		}
	}
	
	@Override
	public String getName() {
		return size + "-phase";
	}
	
	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();
		sb.append(size);
		sb.append("-phase template:\n   ");
		for (int i = 0; i < size; ++i) {
			sb.append("delta_" + i + " > 0\n/\\ ");
		}
		sb.append("( ");
		for (int i = 0; i < size; ++i) {
			if (i > 0) {
				sb.append(" \\/ ");
			}
			sb.append("f_" + i + "(x) > 0");
		}
		sb.append(" )\n");
		for (int i = 0; i < size; ++i) {
			sb.append("/\\ ");
			sb.append(i > 0 ? "( " : "  ");
			sb.append("f_" + i + "(x') < f_" + i + "(x) - delta_" + i);
			if (i > 0) {
				sb.append(" \\/ f_" + (i - 1) + "(x) > 0 )");
			}
			sb.append("\n");
		}
		return sb.toString();
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
		return new MultiphaseRankingFunction(fs);
	}
	
	@Override
	public int getDegree() {
		assert(size > 0);
		return size - 1;
	}

	@Override
	public List<List<LinearInequality>> getConstraintsDec(
			final Map<IProgramVar, TermVariable> inVars, final Map<IProgramVar, TermVariable> outVars) {
		final List<List<LinearInequality>> conjunction =
				new ArrayList<List<LinearInequality>>();
		// f_0(x') < f_0(x) - δ_0
		// /\ /\_{i>0} ( f_i(x') < f_i(x) - δ_i \/ f_{i-1}(x) > 0 )
		for (int i = 0; i < size; ++i) {
			final List<LinearInequality> disjunction = new ArrayList<LinearInequality>();
			final LinearInequality li = mfgens[i].generate(inVars);
			final LinearInequality li2 = mfgens[i].generate(outVars);
			li2.negate();
			li.add(li2);
			final AffineTerm a = new AffineTerm(mdeltas[i], Rational.MONE);
			li.add(a);
			li.setStrict(true);
			li.mMotzkinCoefficient = RED_ATOMS ?
					PossibleMotzkinCoefficients.ZERO_AND_ONE
					: PossibleMotzkinCoefficients.ANYTHING;
			disjunction.add(li);
			if (i > 0) {
				final LinearInequality li3 = mfgens[i - 1].generate(inVars);
				li3.setStrict(true);
				li3.mMotzkinCoefficient = BLUE_ATOMS ?
						PossibleMotzkinCoefficients.ZERO_AND_ONE
						: PossibleMotzkinCoefficients.ANYTHING;
				disjunction.add(li3);
			}
			conjunction.add(disjunction);
		}
		
		// delta_i > 0 is assured by RankingFunctionTemplate.newDelta
		return conjunction;
	}

	@Override
	public List<List<LinearInequality>> getConstraintsNonInc(
			final Map<IProgramVar, TermVariable> inVars, final Map<IProgramVar, TermVariable> outVars) {
		final List<List<LinearInequality>> conjunction =
				new ArrayList<List<LinearInequality>>();
		// f_0(x') ≤ f_0(x) /\ /\_{i>0} ( f_i(x') ≤ f_i(x) \/ f_{i-1}(x) > 0 )
		for (int i = 0; i < size; ++i) {
			final List<LinearInequality> disjunction = new ArrayList<LinearInequality>();
			final LinearInequality li = mfgens[i].generate(inVars);
			final LinearInequality li2 = mfgens[i].generate(outVars);
			li2.negate();
			li.add(li2);
			li.setStrict(false);
			li.mMotzkinCoefficient = RED_ATOMS ?
					PossibleMotzkinCoefficients.ZERO_AND_ONE
					: PossibleMotzkinCoefficients.ANYTHING;
			disjunction.add(li);
			if (i > 0) {
				final LinearInequality li3 = mfgens[i - 1].generate(inVars);
				li3.setStrict(true);
				li3.mMotzkinCoefficient = BLUE_ATOMS ?
						PossibleMotzkinCoefficients.ZERO_AND_ONE
						: PossibleMotzkinCoefficients.ANYTHING;
				disjunction.add(li3);
			}
			conjunction.add(disjunction);
		}
		return conjunction;
	}

	@Override
	public List<List<LinearInequality>> getConstraintsBounded(
			final Map<IProgramVar, TermVariable> inVars, final Map<IProgramVar, TermVariable> outVars) {
		// \/_i f_i(x) > 0
		final List<LinearInequality> disjunction = new ArrayList<LinearInequality>();
		for (int i = 0; i < size; ++i) {
			final LinearInequality li = mfgens[i].generate(inVars);
			li.setStrict(true);
			li.mMotzkinCoefficient = (i == 0 && RED_ATOMS) || (i > 0 && BLUE_ATOMS) ?
					PossibleMotzkinCoefficients.ZERO_AND_ONE
					: PossibleMotzkinCoefficients.ANYTHING;
			disjunction.add(li);
		}
		return Collections.singletonList(disjunction);
	}

	@Override
	public List<String> getAnnotationsDec() {
		final List<String> annotations = new ArrayList<String>();
		for (int i = 0; i < size; ++i) {
			annotations.add("rank f" + i + " is decreasing in phase " + i);
		}
		return annotations;
	}

	@Override
	public List<String> getAnnotationsNonInc() {
		final List<String> annotations = new ArrayList<String>();
		for (int i = 0; i < size; ++i) {
			annotations.add("rank f" + i + " is nonincreasing in phase " + i);
		}
		return annotations;
	}

	@Override
	public List<String> getAnnotationsBounded() {
		return Collections.singletonList("one of the ranks is bounded");
	}
}
