package de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.smt;

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

public class ArrayReadExtractor extends NonRecursive {
	class MyWalker extends TermWalker {
		MyWalker(Term term) { super(term); }
		
		@Override
		public void walk(NonRecursive walker, ConstantTerm term) {
			// do nothing
		}
		@Override
		public void walk(NonRecursive walker, AnnotatedTerm term) {
			walker.enqueueWalker(new MyWalker(term.getSubterm()));
		}
		@Override
		public void walk(NonRecursive walker, ApplicationTerm term) {
			if (term.getFunction().getName().equals("select")) {
				//FIXME: some other function might have the name "select"!?!
				// ask Jochen or Jürgen
				m_ArrayReads.add(term);
			}
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
			// do nothing
		}
	}
	
	Set<Term> m_ArrayReads;
	
	public void compute(Term term) {
		m_ArrayReads = new HashSet<Term>();
		run(new MyWalker(term));
		boolean stop = true;
		m_ArrayReads.toString();
	}
}
