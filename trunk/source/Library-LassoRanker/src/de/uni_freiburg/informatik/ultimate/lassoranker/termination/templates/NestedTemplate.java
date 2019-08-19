/*
 * Copyright (C) 2014-2015 Jan Leike (leike@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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
import de.uni_freiburg.informatik.ultimate.lassoranker.termination.rankingfunctions.NestedRankingFunction;
import de.uni_freiburg.informatik.ultimate.lassoranker.termination.rankingfunctions.RankingFunction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;


/**
 * The nested template finds ranking functions that decrease each iteration
 * by at least the negated value of another function that is also decreasing.
 * 
 * This seems to be a special case of the Polyranking principle introduced
 * by Bradley, Sipma and Manna. We still have to investigate the exact relation. 
 * 
 * <pre>
 *    δ > 0
 * /\ ( f_0(x') < f_0(x) - δ )
 * /\ ( /\_{i > 0} f_i(x') < f_i(x) + f_{i-1}(x) )
 * /\ ( f_n(x) > 0 )
 * </pre>
 * 
 * @author Matthias Heizmann
 */
public class NestedTemplate extends ComposableTemplate {
	
	public final int mSize;
	
	private static final String s_name_delta = "delta_";
	private static final String s_name_function = "rank_";
	
	private Term mdelta;
	private final AffineFunctionGenerator[] mfgens;
	
	/**
	 * @param functions number of linear functions in the nested template
	 */
	public NestedTemplate(final int functions) {
		assert(functions > 1);
		mSize = functions;
		mfgens = new AffineFunctionGenerator[mSize];
	}
	
	@Override
	protected void init() {
		mdelta = newDelta(s_name_delta + getInstanceNumber());
		for (int i = 0; i < mSize; ++i) {
			mfgens[i] = new AffineFunctionGenerator(mScript, mVariables,
					s_name_function + getInstanceNumber() + "_" + i);
		}
	}
	
	@Override
	public String getName() {
		return mSize + "-nested";
	}
	
	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();
		sb.append(mSize);
		sb.append("-nested template:");
		sb.append("\n");
		sb.append("   ");
		sb.append("delta > 0");
		sb.append("\n");
		sb.append("/\\ f_0(x') < f_0(x) - delta");
		sb.append("\n");
		for (int i = 1; i < mSize; ++i) {
			sb.append("/\\ f_" + i + "(x') < f_" + i + "(x) + f_" + (i-1) + "(x)");
			sb.append("\n");
		}
		final int n = mSize-1;
		sb.append("/\\ f_" + n + "(x) > 0");
		return sb.toString();
	}
	
	@Override
	public Collection<Term> getCoefficients() {
		final Collection<Term> list = new ArrayList<Term>();
		list.add(mdelta);
		for (int i = 0; i < mSize; ++i) {
			list.addAll(mfgens[i].getCoefficients());
		}
		return list;
	}

	@Override
	public RankingFunction extractRankingFunction(final Map<Term, Rational> val)
			throws SMTLIBException {
		// The affine-linear functions need a common gcd
		Rational gcd = mfgens[0].getGcd(val);
		for (int i = 1; i < mSize; ++i) {
			gcd = gcd.gcd(mfgens[i].getGcd(val));
		}
		
		final AffineFunction[] fs = new AffineFunction[mSize];
		for (int i = 0; i < mSize; ++i) {
			fs[i] = mfgens[i].extractAffineFunction(val, gcd);
		}
		return new NestedRankingFunction(fs);
	}
	
	@Override
	public int getDegree() {
		return 0;
	}

	@Override
	public List<List<LinearInequality>> getConstraintsDec(
			final Map<IProgramVar, TermVariable> inVars, final Map<IProgramVar, TermVariable> outVars) {
		final List<List<LinearInequality>> conjunction =
				new ArrayList<List<LinearInequality>>();
		// f_0(x') < f_0(x) - δ
		{
			final LinearInequality li = mfgens[0].generate(inVars);
			final LinearInequality li2 = mfgens[0].generate(outVars);
			li2.negate();
			li.add(li2);
			final AffineTerm a = new AffineTerm(mdelta, Rational.MONE);
			li.add(a);
			li.setStrict(true);
			li.mMotzkinCoefficient = RED_ATOMS ?
					PossibleMotzkinCoefficients.ONE
					: PossibleMotzkinCoefficients.ANYTHING;
			conjunction.add(Collections.singletonList(li));
		}
		
		// /\_i f_i(x') < f_i(x) - δ_i + f_{i-1}(x)
		for (int i = 1; i < mSize; ++i) {
			final LinearInequality li = mfgens[i].generate(inVars);
			final LinearInequality li2 = mfgens[i].generate(outVars);
			li2.negate();
			li.add(li2);
			final LinearInequality li3 = mfgens[i-1].generate(inVars);
			li.add(li3);
			li.setStrict(true);
			li.mMotzkinCoefficient = RED_ATOMS ?
					PossibleMotzkinCoefficients.ONE
					: PossibleMotzkinCoefficients.ANYTHING;
			conjunction.add(Collections.singletonList(li));
		}
		
		// delta > 0 is assured by RankingFunctionTemplate.newDelta
		return conjunction;
	}

	@Override
	public List<List<LinearInequality>> getConstraintsNonInc(
			final Map<IProgramVar, TermVariable> inVars, final Map<IProgramVar, TermVariable> outVars) {
		final List<List<LinearInequality>> conjunction =
				new ArrayList<List<LinearInequality>>();
		// /\_i f_i(x') ≤ f_i(x)
		for (int i = 0; i < mSize; ++i) {
			final LinearInequality li = mfgens[i].generate(inVars);
			final LinearInequality li2 = mfgens[i].generate(outVars);
			li2.negate();
			li.add(li2);
			li.setStrict(false);
			li.mMotzkinCoefficient = RED_ATOMS ?
					PossibleMotzkinCoefficients.ONE
					: PossibleMotzkinCoefficients.ANYTHING;
			conjunction.add(Collections.singletonList(li));
		}
		return conjunction;
	}

	@Override
	public List<List<LinearInequality>> getConstraintsBounded(
			final Map<IProgramVar, TermVariable> inVars, final Map<IProgramVar, TermVariable> outVars) {
		// f_n(x) > 0
		final LinearInequality li = mfgens[mSize-1].generate(inVars);
		li.setStrict(true);
		li.mMotzkinCoefficient = RED_ATOMS ?
				PossibleMotzkinCoefficients.ONE
				: PossibleMotzkinCoefficients.ANYTHING;
		return Collections.singletonList(Collections.singletonList(li));
	}

	@Override
	public List<String> getAnnotationsDec() {
		final List<String> annotations = new ArrayList<String>();
		annotations.add("rank f_0 is decreasing");
		for (int i = 0; i < mSize-1; ++i) {
			annotations.add("rank f_" + i + " is decreasing by at least -f_" + (i-1));
		}
		return annotations;
	}

	@Override
	public List<String> getAnnotationsNonInc() {
		final List<String> annotations = new ArrayList<String>();
		for (int i = 0; i < mSize; ++i) {
			annotations.add("rank f_" + i + " is nonincreasing");
		}
		return annotations;
	}

	@Override
	public List<String> getAnnotationsBounded() {
		return Collections.singletonList(
				"rank f_" + (mSize - 1) + " is bounded");
	}
}
