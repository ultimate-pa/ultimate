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

/**
 * Find all subterms that are application terms with FunctionSymbol m_Name.
 * @author Matthias Heizmann
 *
 */
public class ApplicationTermFinder extends NonRecursive {
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
			if (term.getFunction().getName().equals(m_FunctionSymbolName)) {
				m_Result.add(term);
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
	
	
	
	public ApplicationTermFinder(String functionSymbolName) {
		super();
		m_FunctionSymbolName = functionSymbolName;
	}

	private final String m_FunctionSymbolName;
	private Set<ApplicationTerm> m_Result;
	
	public Set<ApplicationTerm> findMatchingSubterms(Term term) {
		m_Result = new HashSet<ApplicationTerm>();
		run(new MyWalker(term));
		return m_Result;
	}
}
