/*
 * Copyright (C) 2009-2012 University of Freiburg
 *
 * This file is part of SMTInterpol.
 *
 * SMTInterpol is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * SMTInterpol is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with SMTInterpol.  If not, see <http://www.gnu.org/licenses/>.
 */
package de.uni_freiburg.informatik.ultimate.smtinterpol.proof;

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
 * Check whether a term would be changed during CNF conversion.  A term is
 * considered "changed" if a proxy literal gets created for this term, a double
 * negation is simplified, or the neutral element of the operator is removed
 * during simplification.
 * @author Juergen Christ
 */
public class CNFTermChecker extends NonRecursive {
	/**
	 * The checker for disjunctions.  A disjunction is already in CNF if the
	 * disjuncts are literals.
	 * @author Juergen Christ
	 */
	public class DisjunctChecker extends TermWalker {

		public DisjunctChecker(Term term) {
			super(term);
		}
		
		@Override
		public void walk(NonRecursive walker, ConstantTerm term) {}

		@Override
		public void walk(NonRecursive walker, AnnotatedTerm term) {
			walker.enqueueWalker(new DisjunctChecker(term.getSubterm()));
		}

		@Override
		public void walk(NonRecursive walker, ApplicationTerm term) {
			if (term.getFunction().isIntern()) {
				String name = term.getFunction().getName();
				if (!name.equals("not"))
					((CNFTermChecker) walker).notCNF();
				else if (term.getParameters()[0] instanceof ApplicationTerm) {
					ApplicationTerm at =
						(ApplicationTerm) term.getParameters()[0];
					if (at.getFunction().isIntern()) {
						if (at.getFunction().getName().equals("=") &&
								at.getFunction().getParameterSort(0) ==
									term.getTheory().getBooleanSort())
							((CNFTermChecker) walker).notCNF();
					}
				} else
					((CNFTermChecker) walker).notCNF();
			}
		}

		@Override
		public void walk(NonRecursive walker, LetTerm term) {
			((CNFTermChecker) walker).notCNF();			
		}

		@Override
		public void walk(NonRecursive walker, QuantifiedFormula term) {
			// TODO what do we do with quantifiers in CNF?
			((CNFTermChecker) walker).notCNF();			
		}

		@Override
		public void walk(NonRecursive walker, TermVariable term) {
			((CNFTermChecker) walker).notCNF();			
		}

	}
	/**
	 * Is the input already in CNF?
	 */
	private boolean m_IsCNF = true;
	/**
	 * Mark the formula to be not in CNF.
	 */
	void notCNF() {
		m_IsCNF = false;
	}
	/**
	 * Is the formula already in CNF?
	 * @return Whether the formula stays the same during CNF conversion.
	 */
	public boolean isCNF() {
		return m_IsCNF;
	}
	/**
	 * Check whether a given term would change during CNF conversion.
	 * @param term The term to check.
	 * @return Whether the formula stays the same during CNF conversion.
	 */
	public boolean check(Term term) {
		super.run(new CNFTermWalker(term));
		return m_IsCNF;
	}
	/**
	 * The actual checker.
	 * @author Juergen Christ
	 */
	private class CNFTermWalker extends NonRecursive.TermWalker {
	
		public CNFTermWalker(Term term) {
			super(term);
		}
	
		@Override
		public void walk(NonRecursive walker, ConstantTerm term) {}
	
		@Override
		public void walk(NonRecursive walker, AnnotatedTerm term) {
			walker.enqueueWalker(new CNFTermWalker(term.getSubterm()));
		}
	
		@Override
		public void walk(NonRecursive walker, ApplicationTerm term) {
			FunctionSymbol fs = term.getFunction();
			if (fs.getDefinition() != null)
				((CNFTermChecker) walker).notCNF();
			else if (fs.getReturnSort() == term.getTheory().getBooleanSort() &&
					fs.isIntern()) {
				if (fs.getName().equals("or")) {
					for (Term t : term.getParameters())
						walker.enqueueWalker(new DisjunctChecker(t));
				} else if (fs.getName().equals("not"))
					walker.enqueueWalker(new DisjunctChecker(term));
				else if (fs.getName().equals("=") &&
						fs.getParameterSort(0) ==
							term.getTheory().getBooleanSort())
					((CNFTermChecker) walker).notCNF();
			} else
				((CNFTermChecker) walker).notCNF();
		}
	
		@Override
		public void walk(NonRecursive walker, LetTerm term) {
			((CNFTermChecker) walker).notCNF();
		}
	
		@Override
		public void walk(NonRecursive walker, QuantifiedFormula term) {
			// TODO what do we do with quantifiers in CNF?
			((CNFTermChecker) walker).notCNF();
		}
	
		@Override
		public void walk(NonRecursive walker, TermVariable term) {
			((CNFTermChecker) walker).notCNF();	
		}
	}
}
