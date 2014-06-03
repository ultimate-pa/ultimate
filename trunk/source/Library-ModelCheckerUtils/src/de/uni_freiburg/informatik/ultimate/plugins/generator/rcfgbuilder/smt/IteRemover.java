package de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.smt;

import java.util.Collections;
import java.util.Iterator;
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
	protected Term transformNonCoreBooleanSubterm(Term term) {
		assert term.getSort().getName().equals("Bool");
		Set<ApplicationTerm> iteSubterms = (new ApplicationTermFinder("ite", true)).findMatchingSubterms(term);
		Term result = rec(term, iteSubterms.iterator());
		assert (Util.checkSat(m_Script, m_Script.term("distinct", 
				term, result)) != LBool.SAT);
		return result;
	}
	
	private Term rec(Term term, Iterator<ApplicationTerm> it) {
		Term result;
		if (it.hasNext()) {
			ApplicationTerm ite = it.next();
			assert ite.getFunction().getName().equals("ite");
			assert ite.getParameters().length == 3;
			Term condition = ite.getParameters()[0];
			Term ifTerm = ite.getParameters()[1];
			Term elseTerm = ite.getParameters()[2];
			Term replacedWithIf;
			{
				Map<Term, Term> substitutionMapping = 
						Collections.singletonMap((Term) ite, ifTerm);
				replacedWithIf = (new SafeSubstitution(
						m_Script, substitutionMapping)).transform(term);
			}
			Term replacedWithElse;
			{
				Map<Term, Term> substitutionMapping = 
						Collections.singletonMap((Term) ite, elseTerm);
				replacedWithElse = (new SafeSubstitution(
						m_Script, substitutionMapping)).transform(term);
			}
			Term withoutThisIte = Util.or(m_Script, 
					Util.and(m_Script, condition, replacedWithIf), 
					Util.and(m_Script, Util.not(m_Script, condition), replacedWithElse)
					);
			result = rec(withoutThisIte, it); 
		} else {
			result = term;
		}
		return result;
	}

}
