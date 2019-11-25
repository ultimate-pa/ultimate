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
import java.util.Collection;
import java.util.Collections;
import java.util.EnumSet;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.linearterms.SolvedBinaryRelation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.polynomial.solve_for_subject.MultiCaseSolvedBinaryRelation.IntricateOperation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.polynomial.solve_for_subject.MultiCaseSolvedBinaryRelation.Xnf;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

/**
 * Builder for {@link MultiCaseSolvedBinaryRelation}.
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 */
public class MultiCaseSolutionBuilder {

	private final Term mSubject;
	private final Xnf mXnf;
	private final Set<TermVariable> mAdditionalAuxiliaryVariables;
	private final Set<IntricateOperation> mAdditionalIntricateOperations;
	private List<Case> mCases;
	private boolean mConstructionFinished = false;

	public MultiCaseSolutionBuilder(final Term subject, final Xnf xnf) {
		super();
		mXnf = xnf;
		mSubject = subject;
		mCases = new ArrayList<Case>();
		mAdditionalAuxiliaryVariables = new HashSet<>();
		mAdditionalIntricateOperations = new HashSet<IntricateOperation>();
	}

	public void conjoinWithConjunction(final Object... newConjuncts) {
		if (mConstructionFinished) {
			throw new IllegalStateException("construction already finished");
		}
		switch (mXnf) {
		case CNF:
			mCases.addAll(buildSingletonCases(newConjuncts));
			break;
		case DNF:
			if (mCases.isEmpty()) {
				mCases.add(new Case(null, Collections.emptySet(), mXnf));
			}
			mCases = buildCopyAndAddToEachCase(mCases, newConjuncts);
			break;
		default:
			throw new AssertionError();
		}
	}

	public void conjoinWithDisjunction(final Object... disjunction) {
		if (mConstructionFinished) {
			throw new IllegalStateException("construction already finished");
		}
		switch (mXnf) {
		case CNF:
			mCases.add(buildCase(disjunction));
			break;
		case DNF:
			if (mCases.isEmpty()) {
				mCases.add(new Case(null, Collections.emptySet(), mXnf));
			}
			mCases = buildProduct(mCases, disjunction);
			break;
		default:
			throw new AssertionError();
		}
	}

	/**
	 * Let the {@link MultiCaseSolutionBuilder} store the conjunction of its
	 * current content and the input of this method. The input of this method is
	 * a disjunctive normal form (DNF) given as a collection of collections. The
	 * inner collections represent conjunctions the outer collection represents
	 * a disjunction of these conjunctions.
	 */
	public void conjoinWithDnf(final Collection<Collection<?>> dnf) {
		if (mConstructionFinished) {
			throw new IllegalStateException("construction already finished");
		}
		switch (mXnf) {
		case CNF:
			throw new UnsupportedOperationException("not yet implemented");
		case DNF:
			final List<Case> resultCases = new ArrayList<Case>();
			for (final Collection<?> conjunction : dnf) {
				if (mCases.isEmpty()) {
					resultCases.add(buildCase(conjunction.toArray()));
				}else {
					resultCases.addAll(buildCopyAndAddToEachCase(mCases, conjunction.toArray()));
				}
			}
			mCases = resultCases;
			break;
		default:
			throw new AssertionError();
		}

	}

	public void reportAdditionalIntricateOperation(final IntricateOperation intricateOperation) {
		mAdditionalIntricateOperations.add(intricateOperation);
	}

	public void reportAdditionalAuxiliaryVariable(final TermVariable auxiliaryVariable) {
		mAdditionalAuxiliaryVariables.add(auxiliaryVariable);
	}

	private Case buildCase(final Object... newElems) throws AssertionError {
		SolvedBinaryRelation solvedBinaryRelation = null;
		final Set<SupportingTerm> supportingTerms = new HashSet<>();
		for (final Object newElem : newElems) {
			if (newElem instanceof SolvedBinaryRelation) {
				if (solvedBinaryRelation == null) {
					solvedBinaryRelation = (SolvedBinaryRelation) newElem;
				} else {
					throw new AssertionError("already have a solvedBinayRelation");
				}
			} else if (newElem instanceof SupportingTerm) {
				supportingTerms.add((SupportingTerm) newElem);
			} else {
				throw new UnsupportedOperationException();
			}
		}
		final Case newCase = new Case(solvedBinaryRelation, supportingTerms, mXnf);
		return newCase;
	}

	private List<Case> buildSingletonCases(final Object... newElems) throws AssertionError {
		final List<Case> result = new ArrayList<Case>();
		for (final Object newElem : newElems) {
			if (newElem instanceof SolvedBinaryRelation) {
				final Case newCase = new Case((SolvedBinaryRelation) newElem, Collections.emptySet(), mXnf);
				result.add(newCase);
			} else if (newElem instanceof SupportingTerm) {
				final Case newCase = new Case(null, Collections.singleton((SupportingTerm) newElem), mXnf);
				result.add(newCase);
			} else {
				throw new UnsupportedOperationException();
			}
		}
		return result;
	}

	/**
	 * Return a copy of the list of cases, where we added the elements newElems
	 * to each case.
	 */
	private List<Case> buildCopyAndAddToEachCase(final List<Case> cases, final Object... newElems) {
		final List<Case> newCases = new ArrayList<>();
		for (final Case c : cases) {
			SolvedBinaryRelation solvedBinaryRelation = null;
			final Set<SupportingTerm> supportingTerms = new HashSet<>(c.getSupportingTerms());
			solvedBinaryRelation = c.getSolvedBinaryRelation();
			for (final Object newElem : newElems) {
				if (newElem instanceof SolvedBinaryRelation) {
					if (solvedBinaryRelation == null) {
						solvedBinaryRelation = (SolvedBinaryRelation) newElem;
					} else {
						throw new AssertionError("already have a solvedBinayRelation");
					}
				} else if (newElem instanceof SupportingTerm) {
					supportingTerms.add((SupportingTerm) newElem);
				} else {
					throw new UnsupportedOperationException();
				}
			}
			final Case newCase = new Case(solvedBinaryRelation, supportingTerms, mXnf);
			newCases.add(newCase);
		}
		return newCases;
	}

	/**
	 * Return a list of cases that contains for each case in the List cases and
	 * each element elem in newElem a copy of the case that contain additionally
	 * elem.
	 */
	private List<Case> buildProduct(final List<Case> cases, final Object... newElems) {
		final List<Case> newCases = new ArrayList<>();
		for (final Case c : cases) {
			for (final Object newElem : newElems) {
				if (c.getSolvedBinaryRelation() != null) {
					throw new AssertionError("already have a solvedBinayRelation");
				}
				if (newElem instanceof SolvedBinaryRelation) {
					final SolvedBinaryRelation solvedBinaryRelation = (SolvedBinaryRelation) newElem;
					final Case newCase = new Case(solvedBinaryRelation, c.getSupportingTerms(), mXnf);
					newCases.add(newCase);
				} else if (newElem instanceof SupportingTerm) {
					final Set<SupportingTerm> newSupportingTerms = new HashSet<>(c.getSupportingTerms());
					newSupportingTerms.add((SupportingTerm) newElem);
					final Case newCase = new Case(c.getSolvedBinaryRelation(), newSupportingTerms, mXnf);
					newCases.add(newCase);
				} else {
					throw new UnsupportedOperationException();
				}
			}
		}
		return newCases;
	}

	public MultiCaseSolvedBinaryRelation buildResult() {
		mConstructionFinished = true;
		final EnumSet<IntricateOperation> additionalIntricateOperations;
		if (mAdditionalIntricateOperations.isEmpty()) {
			additionalIntricateOperations = EnumSet.noneOf(IntricateOperation.class);
		} else {
			additionalIntricateOperations = EnumSet.copyOf(mAdditionalIntricateOperations);
		}
		return new MultiCaseSolvedBinaryRelation(mSubject, mCases, mAdditionalAuxiliaryVariables,
				additionalIntricateOperations, mXnf);
	}
}
