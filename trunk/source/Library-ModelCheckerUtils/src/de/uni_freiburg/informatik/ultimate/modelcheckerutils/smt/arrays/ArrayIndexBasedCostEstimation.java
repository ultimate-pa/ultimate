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
package de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays;

import java.util.ArrayList;
import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.ArrayIndexEqualityManager;
import de.uni_freiburg.informatik.ultimate.util.datastructures.EqualityStatus;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.TreeRelation;

/**
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 */
public class ArrayIndexBasedCostEstimation {

	public static TreeRelation<Integer, TermVariable> computeCostEstimation(final Script script,
			final ArrayIndexEqualityManager aiem, final Set<TermVariable> eliminatees, final Term term) {
		final TreeRelation<Integer, TermVariable> result = new TreeRelation<>();
		for (final TermVariable eliminatee : eliminatees) {
			final Integer costs = computeCostElimation(script, aiem, term, eliminatee);
			result.addPair(costs, eliminatee);
		}
		return result;
	}

	private static int computeCostElimation(final Script script, final ArrayIndexEqualityManager aiem, final Term term,
			final TermVariable eliminatee) {
		final ArrayOccurrenceAnalysis aoa = new ArrayOccurrenceAnalysis(script, term, eliminatee)
				.downgradeDimensionsIfNecessary(script);
		final Set<ArrayIndex> selectIndices = ArrayOccurrenceAnalysis.extractSelectIndices(aoa.getArraySelects());
		final List<ArrayIndex> selectIndicesAsList = new ArrayList<>(selectIndices);
		int totalCost = 0;
		for (int i = 0; i < selectIndicesAsList.size(); i++) {
			for (int j = 0; j < i; j++) {
				final ArrayIndex indexI = selectIndicesAsList.get(i);
				final ArrayIndex indexJ = selectIndicesAsList.get(j);
				final int costForPair = analyzeCosts(aiem, indexI, indexJ);
				totalCost = costForPair + totalCost;
			}
		}
		final Set<ArrayIndex> storeIndices = ArrayOccurrenceAnalysis.extractNestedStoreIndices(aoa.getNestedArrayStores());
		final List<ArrayIndex> storeIndicesAsList = new ArrayList<>(storeIndices);
		for (int i = 0; i < storeIndicesAsList.size(); i++) {
			for (int j = 0; j < selectIndicesAsList.size(); j++) {
				final ArrayIndex indexI = storeIndicesAsList.get(i);
				final ArrayIndex indexJ = selectIndicesAsList.get(j);
				final int costForPair = analyzeCosts(aiem, indexI, indexJ);
				totalCost = costForPair + totalCost;
			}
		}
		return totalCost;
	}

	private static int analyzeCosts(final ArrayIndexEqualityManager aiem, final ArrayIndex indexI, final ArrayIndex indexJ) {
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
