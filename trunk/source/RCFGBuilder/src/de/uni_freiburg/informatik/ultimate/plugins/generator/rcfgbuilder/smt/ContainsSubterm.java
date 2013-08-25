package de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.smt;

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
	class MyWalker extends TermWalker {
		MyWalker(Term term) { super(term); }
		
		@Override
		public void walk(NonRecursive walker, ConstantTerm term) {
			if (!m_FoundInCurrentSeach) {
				if (m_GivenSubterm.equals(term)) {
					m_FoundInCurrentSeach = true;
				} 
			}
		}
		@Override
		public void walk(NonRecursive walker, AnnotatedTerm term) {
			if (!m_FoundInCurrentSeach) {
				if (m_GivenSubterm.equals(term)) {
					m_FoundInCurrentSeach = true;
				} else {
					walker.enqueueWalker(new MyWalker(term.getSubterm()));
				}
			}
		}
		@Override
		public void walk(NonRecursive walker, ApplicationTerm term) {
			if (!m_FoundInCurrentSeach) {
				if (m_GivenSubterm.equals(term)) {
					m_FoundInCurrentSeach = true;
				} 
			} else {
				for (Term t : term.getParameters()) {
					walker.enqueueWalker(new MyWalker(t));
				}
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
			if (!m_FoundInCurrentSeach) {
				if (m_GivenSubterm.equals(term)) {
					m_FoundInCurrentSeach = true;
				} 
			}
		}
	}
	
	private final Term m_GivenSubterm;
	private boolean m_FoundInCurrentSeach;
	
	public ContainsSubterm(Term givenSubterm) {
		super();
		m_GivenSubterm = givenSubterm;
	}

	public boolean containsSubterm(Term term) {
		m_FoundInCurrentSeach = false;
		run(new MyWalker(term));
		return m_FoundInCurrentSeach;
	}
}
