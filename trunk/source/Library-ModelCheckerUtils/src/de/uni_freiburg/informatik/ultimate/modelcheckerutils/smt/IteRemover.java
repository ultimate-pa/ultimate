/*
 * Copyright (C) 2013-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt;

import java.util.Collections;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Util;

/**
 * Transform term into an equivalent term without ite terms. E.g.,
 * a = b ? c : d becomes b && a = c || !b && a = d
 * (= a (ite b c d)) becomes (or (and b (= a c)) (and (not b) (= a d)))
 * 
 * TODO: This could be much more efficient if could obtain the context in which
 * the ite term occurs and check if the condition holds.(Use ideas from 
 * SimplifyDDA). For small formulas we can achieve the same result by applying
 * SimplifyDDA afterwards.
 * @author Matthias Heizmann
 *
 */
public class IteRemover extends NonCoreBooleanSubTermTransformer {
	private final Script m_Script;

	public IteRemover(Script script) {
		super();
		m_Script = script;
	}

	@Override
	protected Term transformNonCoreBooleanSubterm(final Term term) {
		assert term.getSort().getName().equals("Bool");
		Term result = term;
		Set<ApplicationTerm> iteSubterms = (new ApplicationTermFinder("ite", false)).findMatchingSubterms(result);
		while (!iteSubterms.isEmpty()) {
			// remove one ite after another. Cannot naively remove all since
			// one might be subterm of other.
			result = removeIteTerm(result, iteSubterms.iterator().next());
			iteSubterms = (new ApplicationTermFinder("ite", false)).findMatchingSubterms(result);
		}
		assert doesNotContainIteTerm(result) : "not all ite terms were removed";
		assert (Util.checkSat(m_Script, m_Script.term("distinct", 
				term, result)) != LBool.SAT);
		return result;
	}
	
	private boolean doesNotContainIteTerm(Term term) {
		return (new ApplicationTermFinder("ite", true)).findMatchingSubterms(term).isEmpty();
	}

	private Term removeIteTerm(Term term, ApplicationTerm iteTerm) {
		assert iteTerm.getFunction().getName().equals("ite");
		assert iteTerm.getParameters().length == 3;
		Term condition = iteTerm.getParameters()[0];
		Term ifTerm = iteTerm.getParameters()[1];
		Term elseTerm = iteTerm.getParameters()[2];
		Term replacedWithIf;
		{
			Map<Term, Term> substitutionMapping = 
					Collections.singletonMap((Term) iteTerm, ifTerm);
			replacedWithIf = (new SafeSubstitutionWithLocalSimplification(
					m_Script, substitutionMapping)).transform(term);
		}
		Term replacedWithElse;
		{
			Map<Term, Term> substitutionMapping = 
					Collections.singletonMap((Term) iteTerm, elseTerm);
			replacedWithElse = (new SafeSubstitution(
					m_Script, substitutionMapping)).transform(term);
		}
		Term withoutThisIte = Util.or(m_Script, 
				Util.and(m_Script, condition, replacedWithIf), 
				Util.and(m_Script, Util.not(m_Script, condition), replacedWithElse)
				);
		return withoutThisIte;
	}

}
