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

import java.util.Collection;
import java.util.Collections;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.lassoranker.AffineTerm;
import de.uni_freiburg.informatik.ultimate.lassoranker.LinearInequality;
import de.uni_freiburg.informatik.ultimate.lassoranker.LinearInequality.PossibleMotzkinCoefficients;
import de.uni_freiburg.informatik.ultimate.lassoranker.termination.AffineFunction;
import de.uni_freiburg.informatik.ultimate.lassoranker.termination.AffineFunctionGenerator;
import de.uni_freiburg.informatik.ultimate.lassoranker.termination.rankingfunctions.LinearRankingFunction;
import de.uni_freiburg.informatik.ultimate.lassoranker.termination.rankingfunctions.RankingFunction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;


/**
 * The affine template finds an affine-linear ranking function.
 * 
 * Template:
 * <pre>δ > 0 /\ f(x) > 0 /\ f(x') < f(x) - δ</pre>
 * 
 * @author Jan Leike
 */
public class AffineTemplate extends ComposableTemplate {
	
	private static final String s_name_delta = "delta_";
	private static final String s_name_function = "rank_";
	
	private Term mdelta;
	private AffineFunctionGenerator mfgen;
	
	@Override
	protected void init() {
		mdelta = newDelta(s_name_delta + getInstanceNumber());
		mfgen = new AffineFunctionGenerator(mScript, mVariables,
				s_name_function + getInstanceNumber());
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
	public List<List<LinearInequality>> getConstraintsDec(
			final Map<IProgramVar, TermVariable> inVars, final Map<IProgramVar, TermVariable> outVars) {
		// f(x') < f(x) - delta
		final LinearInequality li = mfgen.generate(inVars);
		final LinearInequality li2 = mfgen.generate(outVars);
		li2.negate();
		li.add(li2);
		final AffineTerm a = new AffineTerm(mdelta, Rational.MONE);
		li.add(a);
		li.setStrict(true);
		li.mMotzkinCoefficient = RED_ATOMS ? PossibleMotzkinCoefficients.ONE
				: PossibleMotzkinCoefficients.ANYTHING;
		
		// delta > 0 is assured by RankingFunctionTemplate.newDelta
		return Collections.singletonList(Collections.singletonList(li));
	}

	@Override
	public List<List<LinearInequality>> getConstraintsNonInc(
			final Map<IProgramVar, TermVariable> inVars, final Map<IProgramVar, TermVariable> outVars) {
		// f(x') ≤ f(x)
		final LinearInequality li = mfgen.generate(inVars);
		final LinearInequality li2 = mfgen.generate(outVars);
		li2.negate();
		li.add(li2);
		li.setStrict(false);
		li.mMotzkinCoefficient = RED_ATOMS ? PossibleMotzkinCoefficients.ONE
				: PossibleMotzkinCoefficients.ANYTHING;
		return Collections.singletonList(Collections.singletonList(li));
	}

	@Override
	public List<List<LinearInequality>> getConstraintsBounded(
			final Map<IProgramVar, TermVariable> inVars, final Map<IProgramVar, TermVariable> outVars) {
		// f(x) > 0
		final LinearInequality li = mfgen.generate(inVars);
		li.setStrict(true);
		li.mMotzkinCoefficient = RED_ATOMS ?
				PossibleMotzkinCoefficients.ONE
				: PossibleMotzkinCoefficients.ANYTHING;
		return Collections.singletonList(Collections.singletonList(li));
	}

	@Override
	public List<String> getAnnotationsDec() {
		return Collections.singletonList("rank decreasing");
	}

	@Override
	public List<String> getAnnotationsNonInc() {
		return Collections.singletonList("rank nonincreasing");
	}

	@Override
	public List<String> getAnnotationsBounded() {
		return Collections.singletonList("rank bounded");
	}

	@Override
	public Collection<Term> getCoefficients() {
		final Collection<Term> list = mfgen.getCoefficients();
		list.add(mdelta);
		return list;
	}

	@Override
	public RankingFunction extractRankingFunction(final Map<Term, Rational> val)
			throws SMTLIBException {
		final AffineFunction f = mfgen.extractAffineFunction(val);
		return new LinearRankingFunction(f);
	}
	
	@Override
	public int getDegree() {
		return 0;
	}
}
