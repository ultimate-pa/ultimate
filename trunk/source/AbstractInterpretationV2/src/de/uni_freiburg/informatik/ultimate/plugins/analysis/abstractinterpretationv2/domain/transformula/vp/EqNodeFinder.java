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
package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
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
 * Find the array index by selecting the application term with function "select" and "store".
 * 
 * @author Yu-Wen Chen (yuwenchen1105@gmail.com)
 *
 */
public class EqNodeFinder extends NonRecursive {
	private class  ArrayIndexFindWalker extends TermWalker {
		ArrayIndexFindWalker(Term term) { super(term); }
		
		@Override
		public void walk(NonRecursive walker) {
			if (mVisited.contains(getTerm())) {
				// do nothing
			} else {
				mVisited.add(getTerm());
				super.walk(walker);
			}
		}
		
		@Override
		public void walk(NonRecursive walker, ConstantTerm term) {
			// do nothing
		}
		@Override
		public void walk(NonRecursive walker, AnnotatedTerm term) {
			walker.enqueueWalker(new ArrayIndexFindWalker(term.getSubterm()));
		}
		@Override
		public void walk(NonRecursive walker, ApplicationTerm term) {
			if (term.getFunction().getName() == "select") {
				mResultList.add(new SelectArguments(term, term.getParameters()[0], term.getParameters()[1]));
			} else if (term.getFunction().getName() == "store") {
				mResultList.add(new StoreArguments(term, term.getParameters()[0], term.getParameters()[1], term.getParameters()[2]));
			}
			for (final Term t : term.getParameters()) {
				walker.enqueueWalker(new ArrayIndexFindWalker(t));
			}
		}
		@Override
		public void walk(NonRecursive walker, LetTerm term) {
			throw new UnsupportedOperationException();
		}
		@Override
		public void walk(NonRecursive walker, QuantifiedFormula term) {
			walker.enqueueWalker(new ArrayIndexFindWalker(term.getSubformula()));
		}
		@Override
		public void walk(NonRecursive walker, TermVariable term) {
			// do nothing
		}
	}
	
	public EqNodeFinder() {
		super();
	}

	private List<SelectOrStoreArguments> mResultList;
	private Set<Term> mVisited;
	
	public List<SelectOrStoreArguments> findEqNode(Term term) {
		if (term == null) {
			throw new NullPointerException();
		}
		mVisited = new HashSet<>();
		mResultList = new ArrayList<SelectOrStoreArguments>();
		run(new ArrayIndexFindWalker(term));
		mVisited = null;

		return mResultList;
	}
	
	static class SelectOrStoreArguments {
		final Term originalTerm;
		final Term function;
		final Term arg;
		SelectOrStoreArguments(Term originalTerm, Term function, Term arg) {
			this.originalTerm = originalTerm;
			this.function = function;
			this.arg = arg;
		}
	}

	static class SelectArguments extends SelectOrStoreArguments {
		SelectArguments(Term originalTerm, Term function, Term arg) {
			super(originalTerm, function, arg);
		}
	}
	
	static class StoreArguments extends SelectOrStoreArguments{
		final Term arg2;
		StoreArguments(Term originalTerm, Term function, Term arg, Term arg2) {
			super(originalTerm, function, arg);
			this.arg2 = arg2;
		}
	}
}
