/*
 * Copyright (C) 2019 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2019 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.polynomial.solve_for_subject;

import java.util.ArrayList;
import java.util.EnumSet;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.linearterms.SolvedBinaryRelation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.polynomial.solve_for_subject.MultiCaseSolvedBinaryRelation.IntricateOperation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.polynomial.solve_for_subject.MultiCaseSolvedBinaryRelation.Xnf;
import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 * Builder for {@link MultiCaseSolvedBinaryRelation}.
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 */
public class MultiCaseSolutionBuilder {

	private final Term mSubject;
	private final Xnf mXnf;
	private final Set<IntricateOperation> mAdditionalIntricateOperations;
	private List<Case> mCases;
	private boolean mConstructionFinished = false;

	public MultiCaseSolutionBuilder(final Term subject, final Xnf xnf) {
		super();
		mXnf = xnf;
		mSubject = subject;
		mCases = new ArrayList<Case>();
		mAdditionalIntricateOperations = new HashSet<IntricateOperation>();
	}

	public void conjoinWithConjunction(final Object... newConjuncts) {
		if (mConstructionFinished) {
			throw new IllegalStateException("construction already finished");
		}
		switch (mXnf) {
		case CNF:
			mCases.add(constructCase(newConjuncts));
			break;
		case DNF:
			mCases = addToEachCase(newConjuncts);
			break;
		default:
			throw new AssertionError();
		}
	}

	public void conjoinWithDisjunction(final Object... newConjuncts) {
		if (mConstructionFinished) {
			throw new IllegalStateException("construction already finished");
		}
		switch (mXnf) {
		case CNF:
			mCases = addToEachCase(newConjuncts);
			break;
		case DNF:
			mCases.add(constructCase(newConjuncts));
			break;
		default:
			throw new AssertionError();
		}
	}

	public void reportAdditionalIntricateOperation(final IntricateOperation intricateOperation) {
		mAdditionalIntricateOperations.add(intricateOperation);
	}

	private Case constructCase(final Object... newConjuncts) throws AssertionError {
		SolvedBinaryRelation solvedBinaryRelation = null;
		final Set<SupportingTerm> supportingTerms = new HashSet<>();
		for (final Object newConjunct : newConjuncts) {
			if (newConjunct instanceof SolvedBinaryRelation) {
				if (solvedBinaryRelation == null) {
					solvedBinaryRelation = (SolvedBinaryRelation) newConjunct;
				} else {
					throw new AssertionError("already have a solvedBinayRelation");
				}
			} else if (newConjunct instanceof SupportingTerm) {
				supportingTerms.add((SupportingTerm) newConjunct);
			} else {
				throw new UnsupportedOperationException();
			}
		}
		final Case newCase = new Case(solvedBinaryRelation, supportingTerms, mXnf);
		return newCase;
	}

	private List<Case> addToEachCase(final Object... newKonjuncts) throws AssertionError {
		final List<Case> newCases = new ArrayList<Case>();
		for (final Case c : mCases) {
			SolvedBinaryRelation solvedBinaryRelation = null;
			final Set<SupportingTerm> supportingTerms = new HashSet<>(c.getSupportingTerms());
			solvedBinaryRelation = c.getSolvedBinaryRelation();
			for (final Object newConjunct : newKonjuncts) {
				if (newConjunct instanceof SolvedBinaryRelation) {
					if (solvedBinaryRelation == null) {
						solvedBinaryRelation = (SolvedBinaryRelation) newConjunct;
					} else {
						throw new AssertionError("already have a solvedBinayRelation");
					}
				} else if (newConjunct instanceof SupportingTerm) {
					supportingTerms.add((SupportingTerm) newConjunct);
				} else {
					throw new UnsupportedOperationException();
				}
			}
			final Case newCase = new Case(solvedBinaryRelation, supportingTerms, mXnf);
			newCases.add(newCase);
		}
		return newCases;
	}

	public MultiCaseSolvedBinaryRelation buildResult() {
		mConstructionFinished = true;
		return new MultiCaseSolvedBinaryRelation(mSubject, mCases, EnumSet.copyOf(mAdditionalIntricateOperations), mXnf);
	}
}
