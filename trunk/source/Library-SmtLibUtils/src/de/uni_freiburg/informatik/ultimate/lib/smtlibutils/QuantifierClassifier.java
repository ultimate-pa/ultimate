/*
 * Copyright (C) 2026 Matthias Heizmann (matthias.heizmann@iste.uni-stuttgart.de)
 * Copyright (C) 2026 University of Freiburg
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

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.quantifier.QuantifierUtils.Quantifier;
import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.LambdaTerm;
import de.uni_freiburg.informatik.ultimate.logic.LetTerm;
import de.uni_freiburg.informatik.ultimate.logic.MatchTerm;
import de.uni_freiburg.informatik.ultimate.logic.NonRecursive;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

/**
 * Check which quantifier sequences effective occur in a {@link Term}. E.g., if we have exists not exists, this class
 * detects that we effectively have an EA term. This class is similar to {@link TermClassifier}. But we needed to make a
 * copy of the because for quantifier detection we cannot cache the results of subterms.
 *
 * @author Matthias Heizmann (matthias.heizmann@iste.uni-stuttgart.de)
 *
 */
public class QuantifierClassifier extends NonRecursive {

	private final Set<List<Quantifier>> mLongestQuantSeqs;

	public QuantifierClassifier() {
		mLongestQuantSeqs = new HashSet<>();
	}

	/**
	 * Check a/another Term and add the result to the existing classification results.
	 */
	public void checkTerm(final Term term) {
		run(new MyWalker(false, List.of(), term));
	}

	/**
	 * Check where we allow to consider the term as negated.
	 */
	public void checkTerm(final boolean isNegated, final Term term) {
		run(new MyWalker(isNegated, List.of(), term));
	}

	public Set<List<Quantifier>> getLongestQuantSeqs() {
		return mLongestQuantSeqs;
	}

	public String printLongestQuantSeqs() {
		return String.valueOf(getLongestQuantSeqs().stream().map(this::printQuantSeq).toList());
	}

	private String printQuantSeq(final List<Quantifier> quantSeq) {
		final StringBuilder sb = new StringBuilder();
		for (final Quantifier q : quantSeq) {
			sb.append(q.getAsciiAbbreviation());
		}
		return sb.toString();
	}

	private class MyWalker extends TermWalker {

		private final boolean mIsNegated;
		private final List<Quantifier> mCurrentQuantSeq;

		MyWalker(final boolean isNegated, final List<Quantifier> currentQuantSeq, final Term term) {
			super(term);
			mIsNegated = isNegated;
			mCurrentQuantSeq = currentQuantSeq;
		}

		@Override
		public void walk(final NonRecursive walker, final ConstantTerm term) {
			// cannot descend
		}

		@Override
		public void walk(final NonRecursive walker, final AnnotatedTerm term) {
			walker.enqueueWalker(new MyWalker(mIsNegated, mCurrentQuantSeq, term.getSubterm()));
		}

		@Override
		public void walk(final NonRecursive walker, final ApplicationTerm term) {
			if (term.getFunction().getName().equals("not")) {
				assert term.getParameters().length == 1 : "not term must have exactly one parameter";
				walker.enqueueWalker(new MyWalker(!mIsNegated, mCurrentQuantSeq, term.getParameters()[0]));
			} else {
				for (final Term t : term.getParameters()) {
					walker.enqueueWalker(new MyWalker(mIsNegated, mCurrentQuantSeq, t));
				}
			}
		}

		@Override
		public void walk(final NonRecursive walker, final LetTerm term) {
			throw new UnsupportedOperationException("not yet implemented: LetTerm");
		}

		@Override
		public void walk(final NonRecursive walker, final QuantifiedFormula term) {
			final Quantifier q = Quantifier.of(term.getQuantifier());
			final Quantifier effectiveQuantifier = computeEffectiveQuantifier(q, mIsNegated);

			final List<Quantifier> newQuantSeq;
			if (mCurrentQuantSeq.isEmpty()
					|| mCurrentQuantSeq.get(mCurrentQuantSeq.size() - 1) != effectiveQuantifier) {
				newQuantSeq = new ArrayList<>(mCurrentQuantSeq);
				newQuantSeq.add(effectiveQuantifier);
				// Do not remove existing sequences here; keep sequences from independent
				// subterms even if they are prefixes of the new sequence.
				// If there is an existing sequence that is a supersequence of the new one
				// (i.e., existing starts with newQuantSeq), then the new sequence is redundant.
				final boolean existingIsSupersequence =
						mLongestQuantSeqs.stream().anyMatch(existing -> isSupersequence(newQuantSeq, existing));
				if (!existingIsSupersequence) {
					// Remove any existing sequences that are prefixes of the new sequence,
					// since they are subsumed by the new (longer) sequence.
					mLongestQuantSeqs.removeIf(existing -> isSupersequence(existing, newQuantSeq));
					mLongestQuantSeqs.add(newQuantSeq);
				}
			} else {
				// the quantifier is the same as the last one, no new quantifier alternation
				newQuantSeq = mCurrentQuantSeq;
			}
			walker.enqueueWalker(new MyWalker(mIsNegated, newQuantSeq, term.getSubformula()));

		}

		@Override
		public void walk(final NonRecursive walker, final TermVariable term) {
			// cannot descend
		}

		@Override
		public void walk(final NonRecursive walker, final MatchTerm term) {
			throw new UnsupportedOperationException("not yet implemented: MatchTerm");
		}

		@Override
		public void walk(final NonRecursive walker, final LambdaTerm term) {
			throw new UnsupportedOperationException("Not yet implemented: LambdaTerm");
		}

	}

	private static Quantifier computeEffectiveQuantifier(final Quantifier quantifier, final boolean isNegated) {
		return isNegated ? quantifier.getDualQuantifier() : quantifier;
	}

	/**
	 * Check if big is a supersequence of small. If both are equivalent this is also considered a supersequence.
	 */
	private static boolean isSupersequence(final List<Quantifier> small, final List<Quantifier> big) {
		if (small.size() > big.size()) {
			return false;
		}
		for (int i = 0; i < small.size(); i++) {
			if (small.get(i) != big.get(i)) {
				return false;
			}
		}
		return true;
	}
}
