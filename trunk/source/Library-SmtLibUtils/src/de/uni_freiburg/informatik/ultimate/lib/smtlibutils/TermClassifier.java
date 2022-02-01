/*
 * Copyright (C) 2017 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.lib.smtlibutils;

import java.util.Arrays;
import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials.SolveForSubjectUtils;
import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.LetTerm;
import de.uni_freiburg.informatik.ultimate.logic.MatchTerm;
import de.uni_freiburg.informatik.ultimate.logic.NonRecursive;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

/**
 * Check for a bunch of criteria if they are satisfied by a given {@link Term}.
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
public class TermClassifier extends NonRecursive {

	private Set<Term> mTermsInWhichWeAlreadyDescended;

	private final Set<String> mOccuringSortNames;
	private final Set<String> mOccuringFunctionNames;
	private final Set<Integer> mOccuringQuantifiers;
	private boolean mHasArrays;
	private boolean mHasNonlinearArithmetic;

	public TermClassifier() {
		super();
		mOccuringSortNames = new HashSet<>();
		mOccuringFunctionNames = new HashSet<>();
		mOccuringQuantifiers = new HashSet<>();
		mHasArrays = false;
	}

	public Set<String> getOccuringSortNames() {
		return mOccuringSortNames;
	}

	public Set<String> getOccuringFunctionNames() {
		return mOccuringFunctionNames;
	}

	public Set<Integer> getOccuringQuantifiers() {
		return mOccuringQuantifiers;
	}

	public boolean hasArrays() {
		return mHasArrays;
	}

	public boolean hasNonlinearArithmetic() {
		return mHasNonlinearArithmetic;
	}

	/**
	 * Check a/another Term and add the result to the existing classification results.
	 */
	public void checkTerm(final Term term) {
		mTermsInWhichWeAlreadyDescended = new HashSet<>();
		run(new MyWalker(term));
		mTermsInWhichWeAlreadyDescended = null;
	}

	private class MyWalker extends TermWalker {
		MyWalker(final Term term) {
			super(term);
		}

		@Override
		public void walk(final NonRecursive walker) {
			if (mTermsInWhichWeAlreadyDescended.contains(getTerm())) {
				// do nothing
			} else {
				final Sort currentSort = getTerm().getSort();
				mOccuringSortNames.add(currentSort.getName());
				if (currentSort.isArraySort()) {
					mHasArrays = true;
				}
				if (getTerm() instanceof ApplicationTerm) {
					final ApplicationTerm appTerm = (ApplicationTerm) getTerm();
					if (appTerm.getFunction().getName().equals("*")) {
						final long nonConstantTerms = Arrays.asList(appTerm.getParameters()).stream()
								.filter(x -> !(x instanceof ConstantTerm)).count();
						if (nonConstantTerms > 1) {
							mHasNonlinearArithmetic = true;
						}
					}
					if (appTerm.getFunction().getName().equals("mod")) {
						if (!(appTerm.getParameters()[1] instanceof ConstantTerm)) {
							mHasNonlinearArithmetic = true;
						}
					}
					if (appTerm.getFunction().getName().equals("div")) {
						if (!(SolveForSubjectUtils.tailIsConstant(Arrays.asList(appTerm.getParameters())))) {
							mHasNonlinearArithmetic = true;
						}
					}
				}
				super.walk(walker);
			}
		}

		@Override
		public void walk(final NonRecursive walker, final ConstantTerm term) {
			// cannot descend
		}

		@Override
		public void walk(final NonRecursive walker, final AnnotatedTerm term) {
			mTermsInWhichWeAlreadyDescended.add(term);
			walker.enqueueWalker(new MyWalker(term.getSubterm()));
		}

		@Override
		public void walk(final NonRecursive walker, final ApplicationTerm term) {
			mOccuringFunctionNames.add(term.getFunction().getName());
			mTermsInWhichWeAlreadyDescended.add(term);
			for (final Term t : term.getParameters()) {
				walker.enqueueWalker(new MyWalker(t));
			}
		}

		@Override
		public void walk(final NonRecursive walker, final LetTerm term) {
			mTermsInWhichWeAlreadyDescended.add(term);
			walker.enqueueWalker(new MyWalker(term.getSubTerm()));
			for (final Term v : term.getValues()) {
				walker.enqueueWalker(new MyWalker(v));
			}

		}

		@Override
		public void walk(final NonRecursive walker, final QuantifiedFormula term) {
			mOccuringQuantifiers.add(term.getQuantifier());
			walker.enqueueWalker(new MyWalker(term.getSubformula()));
		}

		@Override
		public void walk(final NonRecursive walker, final TermVariable term) {
			// cannot descend
		}

		@Override
		public void walk(final NonRecursive walker, final MatchTerm term) {
			throw new UnsupportedOperationException("not yet implemented: MatchTerm");
		}
	}
}
