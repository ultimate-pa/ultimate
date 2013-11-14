package de.uni_freiburg.informatik.ultimate.smtinterpol.delta;

import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.LetTerm;
import de.uni_freiburg.informatik.ultimate.logic.NonRecursive;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

public class TermCollector extends NonRecursive {
	
	private final class DepthWalker extends TermWalker {
		
		private int m_Depth;

		public DepthWalker(Term term, int depth) {
			super(term);
			m_Depth = depth;
		}
		
		private boolean isReplaceable(Term t) {
			return !(t instanceof ConstantTerm) && 
					t != t.getTheory().TRUE && t != t.getTheory().FALSE;
		}

		@Override
		public void walk(NonRecursive walker) {
			Term t = getTerm();
			if (m_Depth == TermCollector.this.m_Depth && isReplaceable(t))
				m_Terms.add(t);
			else
				super.walk(walker);
		}

		@Override
		public void walk(NonRecursive walker, ConstantTerm term) {}

		@Override
		public void walk(NonRecursive walker, AnnotatedTerm term) {
			walker.enqueueWalker(
					new DepthWalker(term.getSubterm(), m_Depth + 1));
		}

		@Override
		public void walk(NonRecursive walker, ApplicationTerm term) {
			for (Term p : term.getParameters())
				walker.enqueueWalker(new DepthWalker(p, m_Depth + 1));
		}

		@Override
		public void walk(NonRecursive walker, LetTerm term) {
			for (Term v : term.getValues())
				walker.enqueueWalker(new DepthWalker(v, m_Depth + 1));
			walker.enqueueWalker(
					new DepthWalker(term.getSubTerm(), m_Depth + 1));
		}

		@Override
		public void walk(NonRecursive walker, QuantifiedFormula term) {
			walker.enqueueWalker(
					new DepthWalker(term.getSubformula(), m_Depth + 1));
		}

		@Override
		public void walk(NonRecursive walker, TermVariable term) {}
		
	}

	private int m_Depth;
	private List<Term> m_Terms;
	
	public TermCollector(int depth) {
		m_Depth = depth;
		m_Terms = new ArrayList<Term>();
	}
	
	public void add(Term t) {
		run(new DepthWalker(t, 0));
	}
	
	public List<Term> getTerms() {
		return m_Terms;
	}

}
