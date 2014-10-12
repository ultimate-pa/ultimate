package de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt;

import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.LetTerm;
import de.uni_freiburg.informatik.ultimate.logic.NonRecursive;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

/**
 * Find all NonTheorySymbols that occur freely (not quantified) in a Term.
 * @author Matthias Heizmann
 *
 */
public class NonTheorySymbolFinder extends NonRecursive {
	private class ConstantFindWalker extends TermWalker {
		ConstantFindWalker(Term term) { super(term); }
		
		@Override
		public void walk(NonRecursive walker, ConstantTerm term) {
			// do nothing
		}
		@Override
		public void walk(NonRecursive walker, AnnotatedTerm term) {
			walker.enqueueWalker(new ConstantFindWalker(term.getSubterm()));
		}
		@Override
		public void walk(NonRecursive walker, ApplicationTerm term) {
			if (SmtUtils.isConstant(term)) {
				m_Result.add(new NonTheorySymbol.Constant(term));
			} else {
				FunctionSymbol functionSymbol = term.getFunction();
				if (!functionSymbol.isIntern()) {
					m_Result.add(new NonTheorySymbol.Function(functionSymbol));
				}
			}
			for (Term t : term.getParameters()) {
				walker.enqueueWalker(new ConstantFindWalker(t));
			}
		}
		@Override
		public void walk(NonRecursive walker, LetTerm term) {
			throw new UnsupportedOperationException();
		}
		@Override
		public void walk(NonRecursive walker, QuantifiedFormula term) {
			walker.enqueueWalker(new ConstantFindWalker(term.getSubformula()));
		}
		@Override
		public void walk(NonRecursive walker, TermVariable term) {
			// do nothing
		}
	}
	
	
	
	public NonTheorySymbolFinder() {
		super();
	}

	private Set<NonTheorySymbol<?>> m_Result;
	
	public Set<NonTheorySymbol<?>> findNonTheorySymbols(Term term) {
		if (term == null) {
			throw new NullPointerException();
		}
		m_Result = new HashSet<NonTheorySymbol<?>>();
		run(new ConstantFindWalker(term));
		for (TermVariable tv : term.getFreeVars()) {
			m_Result.add(new NonTheorySymbol.Variable(tv));
		}
		return m_Result;
	}
	
	

}
