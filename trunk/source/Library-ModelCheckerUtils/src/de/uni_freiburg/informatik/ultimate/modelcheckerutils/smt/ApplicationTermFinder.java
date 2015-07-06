/*
 * Copyright (C) 2012-2015 University of Freiburg
 *
 * This file is part of the ULTIMATE Model Checker Utils Library.
 *
 * The ULTIMATE Model Checker Utils Library is free software: you can 
 * redistribute it and/or modify it under the terms of the GNU Lesser General 
 * Public License as published by the Free Software Foundation, either 
 * version 3 of the License, or (at your option) any later version.
 *
 * The ULTIMATE Model Checker Utils Library is distributed in the hope that it
 * will be useful, but WITHOUT ANY WARRANTY; without even the implied warranty 
 * of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Model Checker Utils Library. If not,
 * see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Model Checker Utils Library, or any covered work, 
 * by linking or combining it with Eclipse RCP (or a modified version of
 * Eclipse RCP), containing parts covered by the terms of the Eclipse Public
 * License, the licensors of the ULTIMATE Model Checker Utils Library grant you
 * additional permission to convey the resulting work.
 */
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
 * Find all subterms that are application terms with FunctionSymbol m_Name.
 * The boolean flag m_OnlyOutermost defines if only the outermost occurrence is 
 * returned (m_OnlyOutermost == true) of if each occurrence is returned 
 * (m_OnlyOutermost == false) and hence the result may also contain terms that 
 * are subterms of other result .
 * @author Matthias Heizmann
 *
 */
public class ApplicationTermFinder extends NonRecursive {
	class FindWalker extends TermWalker {
		FindWalker(Term term) { super(term); }
		
		@Override
		public void walk(NonRecursive walker, ConstantTerm term) {
			// do nothing
		}
		@Override
		public void walk(NonRecursive walker, AnnotatedTerm term) {
			walker.enqueueWalker(new FindWalker(term.getSubterm()));
		}
		@Override
		public void walk(NonRecursive walker, ApplicationTerm term) {
			if (term.getFunction().getName().equals(m_FunctionSymbolName)) {
				m_Result.add(term);
				if (m_OnlyOutermost) {
					return;
				}
			}
			for (Term t : term.getParameters()) {
				walker.enqueueWalker(new FindWalker(t));
			}
		}
		@Override
		public void walk(NonRecursive walker, LetTerm term) {
			throw new UnsupportedOperationException();
		}
		@Override
		public void walk(NonRecursive walker, QuantifiedFormula term) {
			walker.enqueueWalker(new FindWalker(term.getSubformula()));
		}
		@Override
		public void walk(NonRecursive walker, TermVariable term) {
			// do nothing
		}
	}
	
	
	
	public ApplicationTermFinder(String functionSymbolName, boolean onlyOutermost) {
		super();
		m_FunctionSymbolName = functionSymbolName;
		m_OnlyOutermost = onlyOutermost;
	}

	private final String m_FunctionSymbolName;
	private Set<ApplicationTerm> m_Result;
	private final boolean m_OnlyOutermost;
	
	public Set<ApplicationTerm> findMatchingSubterms(Term term) {
		if (term == null) {
			throw new NullPointerException();
		}
		m_Result = new HashSet<ApplicationTerm>();
		run(new FindWalker(term));
		return m_Result;
	}
}
