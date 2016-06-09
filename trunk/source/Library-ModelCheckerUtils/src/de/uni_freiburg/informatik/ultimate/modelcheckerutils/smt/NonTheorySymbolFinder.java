/*
 * Copyright (C) 2014-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE ModelCheckerUtils Library.
 * 
 * The ULTIMATE ModelCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE ModelCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ModelCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ModelCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE ModelCheckerUtils Library grant you additional permission 
 * to convey the resulting work.
 */
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
			if (mVisitedSubterms.contains(term)) {
				// subterm already visited, we will not find anything new
				return;
			} else {
				mVisitedSubterms.add(term);
				if (SmtUtils.isConstant(term)) {
					mResult.add(new NonTheorySymbol.Constant(term));
				} else {
					final FunctionSymbol functionSymbol = term.getFunction();
					if (!functionSymbol.isIntern()) {
						mResult.add(new NonTheorySymbol.Function(functionSymbol));
					}
				}
				for (final Term t : term.getParameters()) {
					walker.enqueueWalker(new ConstantFindWalker(t));
				}
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

	private Set<NonTheorySymbol<?>> mResult;
	private Set<Term> mVisitedSubterms;
	
	public Set<NonTheorySymbol<?>> findNonTheorySymbols(Term term) {
		if (term == null) {
			throw new NullPointerException();
		}
		mResult = new HashSet<NonTheorySymbol<?>>();
		mVisitedSubterms = new HashSet<>();
		run(new ConstantFindWalker(term));
		for (final TermVariable tv : term.getFreeVars()) {
			mResult.add(new NonTheorySymbol.Variable(tv));
		}
		return mResult;
	}
	
	

}
