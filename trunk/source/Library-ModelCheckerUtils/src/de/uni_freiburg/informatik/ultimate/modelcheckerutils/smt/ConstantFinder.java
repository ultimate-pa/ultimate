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
 * Find all application terms with zero parameters (this is our representation
 * of a constant).
 * In the future  we  may extend this class to all uninterpreted functions.
 * @author Matthias Heizmann
 *
 */
public class ConstantFinder extends NonRecursive {
	class ConstantFindWalker extends TermWalker {
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
			if (isConstant(term)) {
				m_Result.add(term);
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
	
	
	
	public ConstantFinder() {
		super();
	}

	private Set<ApplicationTerm> m_Result;
	
	public Set<ApplicationTerm> findConstants(Term term) {
		if (term == null) {
			throw new NullPointerException();
		}
		m_Result = new HashSet<ApplicationTerm>();
		run(new ConstantFindWalker(term));
		return m_Result;
	}
	
	
	/**
	 * A constant is an ApplicationTerm with zero parameters whose function
	 * symbol is not intern.
	 */
	public static boolean isConstant(ApplicationTerm term) {
		return term.getParameters().length == 0 && !term.getFunction().isIntern();
	}
}
