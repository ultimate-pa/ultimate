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

import de.uni_freiburg.informatik.ultimate.lassoranker.LinearInequality;
import de.uni_freiburg.informatik.ultimate.lassoranker.termination.rankingfunctions.LexicographicRankingFunction;
import de.uni_freiburg.informatik.ultimate.lassoranker.termination.rankingfunctions.RankingFunction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;


/**
 * A composed lexicographic template is a ranking template that
 * corresponds to a lexicographic ranking function where
 * each entry is a ranking function from a composable template.
 * 
 * @author Jan Leike
 */
public class ComposedLexicographicTemplate extends ComposableTemplate {
	
	ComposableTemplate[] mParts;
	
	/**
	 * Construct a new ComposedLexicographicTemplate
	 * 
	 * @param parts the ranking templates that are used as lexicographic entries
	 */
	public ComposedLexicographicTemplate(final ComposableTemplate[] parts) {
		assert(parts.length >= 1);
		mParts = parts;
	}
	
	@Override
	protected void init() {
		for (final ComposableTemplate t : mParts) {
			t.init(mTAS);
		}
	}
	
	@Override
	public String getName() {
		final StringBuilder sb = new StringBuilder();
		sb.append("lex(");
		boolean first = true;
		for (final ComposableTemplate t : mParts) {
			if (!first) {
				sb.append(", ");
			}
			sb.append(t.getName());
			first = false;
		}
		sb.append(")");
		return sb.toString();
	}

	@Override
	public List<List<LinearInequality>> getConstraintsDec(
			final Map<IProgramVar, TermVariable> inVars, final Map<IProgramVar, TermVariable> outVars) {
		final List<List<List<List<LinearInequality>>>> constraints =
				new ArrayList<List<List<List<LinearInequality>>>>();
		
		// \/_i T_i^<
		{
			final List<List<List<LinearInequality>>> disjunction =
					new ArrayList<List<List<LinearInequality>>>();
			for (final ComposableTemplate t : mParts) {
				disjunction.add(t.getConstraintsDec(inVars, outVars));
			}
			constraints.add(disjunction);
		}
		
		// /\_{i<k-1} (T_i^≤ \/ \/_{j < i} T_j^<)
		for (int i = 0; i < mParts.length - 1; ++i) {
			final List<List<List<LinearInequality>>> disjunction =
					new ArrayList<List<List<LinearInequality>>>();
			disjunction.add(mParts[i].getConstraintsNonInc(inVars, outVars));
			for (int j = 0; j < i; ++j) {
				disjunction.add(mParts[j].getConstraintsDec(inVars, outVars));
			}
			constraints.add(disjunction);
		}
		
		final List<List<LinearInequality>> cnf =
				TemplateComposition.distribute(constraints);
		TemplateComposition.resetMotzkin(cnf);
		return cnf;
	}


	@Override
	public List<List<LinearInequality>> getConstraintsNonInc(
			final Map<IProgramVar, TermVariable> inVars, final Map<IProgramVar, TermVariable> outVars) {
		final List<List<List<List<LinearInequality>>>> constraints =
				new ArrayList<List<List<List<LinearInequality>>>>();
		// /\_i (T_i^≤ \/ \/_{j < i} T_j^<)
		for (int i = 0; i < mParts.length; ++i) {
			final List<List<List<LinearInequality>>> disjunction =
					new ArrayList<List<List<LinearInequality>>>();
			disjunction.add(mParts[i].getConstraintsNonInc(inVars, outVars));
			for (int j = 0; j < i; ++j) {
				disjunction.add(mParts[j].getConstraintsDec(inVars, outVars));
			}
			constraints.add(disjunction);
		}
		
		final List<List<LinearInequality>> cnf =
				TemplateComposition.distribute(constraints);
		TemplateComposition.resetMotzkin(cnf);
		return cnf;
	}

	@Override
	public List<List<LinearInequality>> getConstraintsBounded(
			final Map<IProgramVar, TermVariable> inVars, final Map<IProgramVar, TermVariable> outVars) {
		final List<List<List<List<LinearInequality>>>> constraints =
				new ArrayList<List<List<List<LinearInequality>>>>();
		
		// /\_i T_i^{>0}
		for (final ComposableTemplate t : mParts) {
			constraints.add(Collections.singletonList(
					t.getConstraintsBounded(inVars, outVars)));
		}
		
		final List<List<LinearInequality>> cnf =
				TemplateComposition.distribute(constraints);
		TemplateComposition.resetMotzkin(cnf);
		return cnf;
	}

	private List<String> blankAnnotations(final int size) {
		final List<String> annotations = new ArrayList<String>(size);
		for (int i = 0; i < size; ++i) {
			annotations.add("");
		}
		return annotations;
	}

	@Override
	public List<String> getAnnotationsDec() {
		// TODO
		final Map<IProgramVar, TermVariable> empty = Collections.emptyMap();
		return blankAnnotations(getConstraintsDec(empty, empty).size());
	}


	@Override
	public List<String> getAnnotationsNonInc() {
		// TODO
		final Map<IProgramVar, TermVariable> empty = Collections.emptyMap();
		return blankAnnotations(getConstraintsNonInc(empty, empty).size());
	}

	@Override
	public List<String> getAnnotationsBounded() {
		// TODO
		final Map<IProgramVar, TermVariable> empty = Collections.emptyMap();
		return blankAnnotations(getConstraintsBounded(empty, empty).size());
	}
	
	@Override
	public String toString() {
		return ""; // TODO
	}
	
	@Override
	public Collection<Term> getCoefficients() {
		final List<Term> variables = new ArrayList<Term>();
		for (final ComposableTemplate t : mParts) {
			variables.addAll(t.getCoefficients());
		}
		return variables;
	}

	@Override
	public int getDegree() {
		final Map<IProgramVar, TermVariable> empty = Collections.emptyMap();
		return TemplateComposition.computeDegree(getConstraintsBounded(empty, empty))
				+ TemplateComposition.computeDegree(getConstraintsDec(empty, empty));
	}

	@Override
	public RankingFunction extractRankingFunction(final Map<Term, Rational> val)
			throws SMTLIBException {
		final RankingFunction[] rfs = new RankingFunction[mParts.length];
		for (int i = 0; i < mParts.length; ++i) {
			rfs[i] = mParts[i].extractRankingFunction(val);
		}
		return new LexicographicRankingFunction(rfs);
	}
}
