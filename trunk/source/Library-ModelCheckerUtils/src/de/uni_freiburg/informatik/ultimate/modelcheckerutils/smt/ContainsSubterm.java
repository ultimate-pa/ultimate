package de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt;

import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.LetTerm;
import de.uni_freiburg.informatik.ultimate.logic.NonRecursive;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

/**
 * Check if term contains given subterm.
 * @author Matthias Heizmann
 *
 */
public class ContainsSubterm extends NonRecursive {
	
	private Set<Term> m_TermsInWhichWeAlreadyDescended;
	
	class MyWalker extends TermWalker {
		MyWalker(Term term) { super(term); }
		
		@Override
		public void walk(NonRecursive walker) {
			if (m_FoundInCurrentSeach) {
				// do nothing
			} else {
				if (m_TermsInWhichWeAlreadyDescended.contains(getTerm())) {
					// do nothing
				} else {
					if (m_GivenSubterm.equals(getTerm())) {
						m_FoundInCurrentSeach = true;
						reset();
					} else {
						super.walk(walker);
					}
				}
			}
		}




		@Override
		public void walk(NonRecursive walker, ConstantTerm term) {
			// cannot descend
		}
		@Override
		public void walk(NonRecursive walker, AnnotatedTerm term) {
			m_TermsInWhichWeAlreadyDescended.add(term);
			walker.enqueueWalker(new MyWalker(term.getSubterm()));
		}
		@Override
		public void walk(NonRecursive walker, ApplicationTerm term) {
			m_TermsInWhichWeAlreadyDescended.add(term);
			for (Term t : term.getParameters()) {
				walker.enqueueWalker(new MyWalker(t));
			}
		}
		@Override
		public void walk(NonRecursive walker, LetTerm term) {
			throw new UnsupportedOperationException();
		}
		@Override
		public void walk(NonRecursive walker, QuantifiedFormula term) {
			throw new UnsupportedOperationException();
		}
		@Override
		public void walk(NonRecursive walker, TermVariable term) {
			// cannot descend
		}
	}
	
	private final Term m_GivenSubterm;
	private boolean m_FoundInCurrentSeach;
	
	public ContainsSubterm(Term givenSubterm) {
		super();
		m_GivenSubterm = givenSubterm;
	}

	/**
	 * Returns true iff this term contains the subterm of this ContainsSubterm 
	 * object.
	 */
	public boolean containsSubterm(Term term) {
		m_FoundInCurrentSeach = false;
		m_TermsInWhichWeAlreadyDescended = new HashSet<>();
		run(new MyWalker(term));
		m_TermsInWhichWeAlreadyDescended = null;
		return m_FoundInCurrentSeach;
	}
}
