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
			replacedWithIf = (new SafeSubstitution(
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
