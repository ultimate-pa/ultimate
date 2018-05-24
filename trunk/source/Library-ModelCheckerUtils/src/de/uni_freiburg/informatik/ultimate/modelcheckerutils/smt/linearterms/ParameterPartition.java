/*
 * Copyright (C) 2016 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
 * 
 * This file is part of the ULTIMATE ModelCheckerUtils Library.
 * 
 * The ULTIMATE ModelCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE ModelCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ModelCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ModelCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE ModelCheckerUtils Library grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.linearterms;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.QuantifierUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.UnionFind;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

/**
 * Assume we have a quantified term in which we cannot trivially push 
 * the quantifier further because we have
 * - an existentially quantified conjunction, or
 * - an universally quantified disjunction.
 * We partition the parameters of the conjunction (resp. disjunction) such that
 * two parameters are equivalent if some quantified variable occurs in both.
 * If the resulting partition is not trivial (i.e., does not consist of a single
 * equivalence class) we push the quantifier one step such that we
 * obtain a conjunction (resp. disjunction) that has one param for each
 * equivalence class. The param is a quantified formula whose variables
 * are those that occur in the equivalence class
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
public class ParameterPartition {
	
	private final boolean mIsPartitionTrivial;
	private Term mTermWithPushedQuantifier;

	public ParameterPartition(final Script script, final QuantifiedFormula quantifiedFormula) {
		final int quantifier = quantifiedFormula.getQuantifier();
		final Term subformula = quantifiedFormula.getSubformula();
		if (!(subformula instanceof ApplicationTerm)) {
			throw new IllegalArgumentException();
		}
		final ApplicationTerm appTerm = (ApplicationTerm) subformula;
		final String connective = appTerm.getFunction().getApplicationString();
		if (!connective.equals(SmtUtils.getCorrespondingFiniteConnective(SmtUtils.getOtherQuantifier(quantifier)))) {
			throw new IllegalArgumentException("expecting and for exists and or for all");
		}
		final Term[] params = QuantifierUtils.getXjunctsInner(quantifier, appTerm);
		final Set<TermVariable> quantifiedVars = new HashSet<>(Arrays.asList(quantifiedFormula.getVariables()));
		
		final HashRelation<TermVariable, Term> quantifiedVars2param = new HashRelation<>();
		final HashRelation<Term, TermVariable> param2quantifiedVars = new HashRelation<>();
		final UnionFind<Term> uf = new UnionFind<>();
		for (final Term xjunct : params) {
			for (final TermVariable tv : xjunct.getFreeVars()) {
				if (quantifiedVars.contains(tv)) {
					quantifiedVars2param.addPair(tv, xjunct);
					param2quantifiedVars.addPair(xjunct, tv);
				}
			}
			uf.makeEquivalenceClass(xjunct);
		}
		
		for (final TermVariable tv : quantifiedVars2param.getDomain()) {
			uf.union(quantifiedVars2param.getImage(tv));
		}
		
		final Collection<Set<Term>> equivalenceClasses = uf.getAllEquivalenceClasses();
		mIsPartitionTrivial = (equivalenceClasses.size() == 1);
		if (!mIsPartitionTrivial) {
			final List<Term> resultParams = new ArrayList<>(equivalenceClasses.size());
			for (final Set<Term> equivalenceClass : equivalenceClasses) {
				final Set<TermVariable> quantifiedVarsInClass = new HashSet<>();
				for (final Term term : equivalenceClass) {
					quantifiedVarsInClass.addAll(param2quantifiedVars.getImage(term));
				}
				final Term connectedEquivalenceClass = QuantifierUtils.applyDualFiniteConnective(
						script, quantifier, equivalenceClass);
				final Term quantified = SmtUtils.quantifier(script, quantifier, quantifiedVarsInClass, connectedEquivalenceClass);
				resultParams.add(quantified);
			}
			mTermWithPushedQuantifier = QuantifierUtils.applyDualFiniteConnective(script, quantifier, resultParams);
		}
		
		
	}

	public boolean isIsPartitionTrivial() {
		return mIsPartitionTrivial;
	}

	public Term getTermWithPushedQuantifier() {
		return mTermWithPushedQuantifier;
	}

}
