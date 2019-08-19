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
package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.arrays;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.ArrayIndexEqualityManager;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.util.datastructures.Doubleton;
import de.uni_freiburg.informatik.ultimate.util.datastructures.EqualityStatus;
import de.uni_freiburg.informatik.ultimate.util.datastructures.MultiElementCounter;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.TreeRelation;

/**
 * Compute rough estimation of the expected costs of a quantifier elimination.
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 */
public class ArrayIndexBasedCostEstimation {
	private final MultiElementCounter<Doubleton<ArrayIndex>> mIndexDoubleton2Occurrence = new MultiElementCounter<Doubleton<ArrayIndex>>();
	private final MultiElementCounter<TermVariable> mEliminatee2Cost = new MultiElementCounter<TermVariable>();
	private final TreeRelation<Integer, TermVariable> mCost2Eliminatee;
	private final TreeRelation<Integer, Doubleton<ArrayIndex>> mOccurrence2Doubletons;
	private final int mOccurrenceMaximum;
	private final Doubleton<Term> mProposedCaseSplitDoubleton;

	/**
	 * @param forbiddenVariables
	 *            Variables that must not occur in the index entry pairs that are
	 *            used to propose a case split
	 */
	public ArrayIndexBasedCostEstimation(final Script script, final ArrayIndexEqualityManager aiem,
			final Set<TermVariable> eliminatees, final Term term, final Set<TermVariable> forbiddenVariables) {
		for (final TermVariable eliminatee : eliminatees) {
			computeCostEstimation(script, aiem, term, eliminatee);
		}
		mCost2Eliminatee = computeCost2Eliminatee(eliminatees, mEliminatee2Cost);
		mOccurrence2Doubletons = computeOccurrence2Doubletons(mIndexDoubleton2Occurrence);
		if (mOccurrence2Doubletons.isEmpty()) {
			mOccurrenceMaximum = 0;
			mProposedCaseSplitDoubleton = null;
		} else {
			mOccurrenceMaximum = mOccurrence2Doubletons.descendingDomain().iterator().next();
			mProposedCaseSplitDoubleton = computeProposedCaseSplitDoubleton(aiem, forbiddenVariables, mOccurrence2Doubletons,
					mOccurrenceMaximum);
		}
	}

	private Doubleton<Term> computeProposedCaseSplitDoubleton(final ArrayIndexEqualityManager aiem,
			final Set<TermVariable> forbiddenVariables,
			final TreeRelation<Integer, Doubleton<ArrayIndex>> occurrence2Doubletons, final int occurrenceMaximum) {
		for (final Doubleton<ArrayIndex> indexDoubleton : occurrence2Doubletons.getImage(occurrenceMaximum)) {
			for (int i = 0; i < indexDoubleton.getOneElement().size(); i++) {
				final Term entry1 = indexDoubleton.getOneElement().get(i);
				final Term entry2 = indexDoubleton.getOtherElement().get(i);
//				if (Collections.disjoint(forbiddenVariables, Arrays.asList(entry1.getFreeVars())) &&
//						Collections.disjoint(forbiddenVariables, Arrays.asList(entry2.getFreeVars()))) {
					final EqualityStatus es = aiem.checkEqualityStatus(entry1, entry2);
					if (es == EqualityStatus.UNKNOWN) {
						return new Doubleton<Term>(entry1, entry2);

					}
//				}
			}
		}
//		return null;
		throw new AssertionError("all values known");
	}

	public TreeRelation<Integer, TermVariable> getCost2Eliminatee() {
		return mCost2Eliminatee;
	}

	public int getOccurrenceMaximum() {
		return mOccurrenceMaximum;
	}

	public Doubleton<Term> getProposedCaseSplitDoubleton() {
		return mProposedCaseSplitDoubleton;
	}

	private static TreeRelation<Integer, TermVariable> computeCost2Eliminatee(final Set<TermVariable> eliminatees,
			final MultiElementCounter<TermVariable> eliminatee2Cost) {
		final TreeRelation<Integer, TermVariable> result = new TreeRelation<>();
		for (final TermVariable eliminatee : eliminatees) {
			result.addPair(eliminatee2Cost.getNumber(eliminatee), eliminatee);
		}
		return result;
	}

	private static TreeRelation<Integer, Doubleton<ArrayIndex>> computeOccurrence2Doubletons(
			final MultiElementCounter<Doubleton<ArrayIndex>> indexDoubleton2Occurrence) {
		final TreeRelation<Integer, Doubleton<ArrayIndex>> result = new TreeRelation<>();
		for (final Doubleton<ArrayIndex> elem : indexDoubleton2Occurrence.getElements()) {
			result.addPair(indexDoubleton2Occurrence.getNumber(elem), elem);
		}
		return result;
	}

	private void computeCostEstimation(final Script script, final ArrayIndexEqualityManager aiem, final Term term,
			final TermVariable eliminatee) {
		final ArrayOccurrenceAnalysis aoa = new ArrayOccurrenceAnalysis(script, term, eliminatee)
				.downgradeDimensionsIfNecessary(script);

		final Set<ArrayIndex> selectIndicesIntroducedBySos = new HashSet<>();
		final List<MultiDimensionalSelectOverNestedStore> arraySelectOverStores = aoa.getArraySelectOverStores();
		for (final MultiDimensionalSelectOverNestedStore sos : arraySelectOverStores) {
			final ArrayIndex selectIdx = sos.getSelect().getIndex();
			final List<ArrayIndex> nsi = sos.getNestedStore().getIndices();
			final boolean earlyResultDetection = sosOuterLoop(aiem, eliminatee, selectIdx, nsi);
			if (!earlyResultDetection) {
				selectIndicesIntroducedBySos.add(selectIdx);
			}
		}

		final Set<ArrayIndex> selectIndices = ArrayOccurrenceAnalysis.extractSelectIndices(aoa.getArraySelects());
		final List<ArrayIndex> selectIndicesAsList = new ArrayList<>(selectIndices);
		selectIndicesAsList.addAll(selectIndicesIntroducedBySos);
		for (int i = 0; i < selectIndicesAsList.size(); i++) {
			for (int j = 0; j < i; j++) {
				final ArrayIndex indexI = selectIndicesAsList.get(i);
				final ArrayIndex indexJ = selectIndicesAsList.get(j);
				final int costForPair = analyzeCosts(aiem, indexI, indexJ);
				if (costForPair != 0) {
					mIndexDoubleton2Occurrence.increment(new Doubleton<ArrayIndex>(indexI, indexJ), costForPair);
					mEliminatee2Cost.increment(eliminatee, costForPair);
				}

			}
		}
		final Set<ArrayIndex> storeIndices = ArrayOccurrenceAnalysis
				.extractNestedStoreIndices(aoa.getNestedArrayStores());
		final List<ArrayIndex> storeIndicesAsList = new ArrayList<>(storeIndices);
		for (int i = 0; i < storeIndicesAsList.size(); i++) {
			for (int j = 0; j < selectIndicesAsList.size(); j++) {
				final ArrayIndex indexI = storeIndicesAsList.get(i);
				final ArrayIndex indexJ = selectIndicesAsList.get(j);
				final int costForPair = analyzeCosts(aiem, indexI, indexJ);
				if (costForPair != 0) {
					mIndexDoubleton2Occurrence.increment(new Doubleton<ArrayIndex>(indexI, indexJ), costForPair);
					mEliminatee2Cost.increment(eliminatee, costForPair);
				}
			}
		}
	}

	private boolean sosOuterLoop(final ArrayIndexEqualityManager aiem, final TermVariable eliminatee,
			final ArrayIndex selectIdx, final List<ArrayIndex> nsi) {
		for (int indexOfEquality = nsi.size() - 1; indexOfEquality >= 0; indexOfEquality--) {
			final boolean earlyResultDetection = sosInnerLoop(aiem, selectIdx, nsi, indexOfEquality);
			// we need another disjunct/conjunct in result
			mEliminatee2Cost.increment(eliminatee);
			if (earlyResultDetection) {
				return true;
			}
		}
		return false;
	}

	private boolean sosInnerLoop(final ArrayIndexEqualityManager aiem, final ArrayIndex selectIdx,
			final List<ArrayIndex> nsi, final int indexOfEquality) {
		for (int i = nsi.size() - 1; i >= indexOfEquality; i--) {
			final EqualityStatus eq = aiem.checkIndexEquality(selectIdx, nsi.get(i));
			switch (eq) {
			case EQUAL:
				return true;
			case NOT_EQUAL:
				break;
			case UNKNOWN:
				mIndexDoubleton2Occurrence.increment(new Doubleton<ArrayIndex>(selectIdx, nsi.get(i)));
				break;
			default:
				throw new AssertionError();
			}
		}
		return false;
	}

	private static int analyzeCosts(final ArrayIndexEqualityManager aiem, final ArrayIndex indexI,
			final ArrayIndex indexJ) {
		if (indexI.size() != indexJ.size()) {
			throw new AssertionError("incompatible size");
		}
		int unknowns = 0;
		for (int k = 0; k < indexI.size(); k++) {
			final Term entryI = indexI.get(k);
			final Term entryJ = indexJ.get(k);
			final EqualityStatus eq = aiem.checkEqualityStatus(entryI, entryJ);
			switch (eq) {
			case EQUAL:
				// do nothing
				break;
			case NOT_EQUAL:
				return 0;
			case UNKNOWN:
				unknowns++;
				break;
			default:
				break;
			}
		}
		return unknowns;
	}

}
