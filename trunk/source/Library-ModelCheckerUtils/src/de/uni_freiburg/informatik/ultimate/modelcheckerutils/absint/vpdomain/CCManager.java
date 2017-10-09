/*
 * Copyright (C) 2017 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
 *
 * This file is part of the ULTIMATE AbstractInterpretationV2 plug-in.
 *
 * The ULTIMATE AbstractInterpretationV2 plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE AbstractInterpretationV2 plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE AbstractInterpretationV2 plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE AbstractInterpretationV2 plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE AbstractInterpretationV2 plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.modelcheckerutils.absint.vpdomain;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.Map.Entry;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.util.datastructures.CongruenceClosure;
import de.uni_freiburg.informatik.ultimate.util.datastructures.CrossProducts;
import de.uni_freiburg.informatik.ultimate.util.datastructures.UnionFind;
import de.uni_freiburg.informatik.ultimate.util.datastructures.poset.IPartialComparator;
import de.uni_freiburg.informatik.ultimate.util.datastructures.poset.IPartialComparator.ComparisonResult;
import de.uni_freiburg.informatik.ultimate.util.datastructures.poset.PosetUtils;

class CCManager<NODE extends IEqNodeIdentifier<NODE>> {
	private final IPartialComparator<CongruenceClosure<NODE>> mCcComparator;

	public CCManager(final IPartialComparator<CongruenceClosure<NODE>> ccComparator) {
		mCcComparator = ccComparator;
	}

	CongruenceClosure<NODE> getMeet(final CongruenceClosure<NODE> cc1,
			final CongruenceClosure<NODE> cc2) {
		/*
		 *  TODO: something smarter
		 *   ideas:
		 *    - caching
		 *    - updating meets alongside inputs (something that updates the cache on a report equality on the ground pa)
		 *
		 */
		final CongruenceClosure<NODE> result = cc1.meetRec(cc2);
		return result;
	}

	public ComparisonResult compare(final CongruenceClosure<NODE> cc1,
			final CongruenceClosure<NODE> cc2) {
		return mCcComparator.compare(cc1, cc2);

	}

	/**
	 * The given list is implictly a disjunction.
	 * If one element in the disjunction is stronger than another, we can drop it.
	 *
	 * TODO: poor man's solution, could be done much nicer with lattice representation..
	 *
	 * @param unionList
	 * @return
	 */
	public List<CongruenceClosure<NODE>> filterRedundantCcs(final List<CongruenceClosure<NODE>> unionList) {
		// TODO: check if this is a performance bottleneck
		final List<CongruenceClosure<NODE>> filteredForWeaker =
				PosetUtils.filterMaximalElements(unionList, mCcComparator).collect(Collectors.toList());

		/*
		 * drop all but one equivalent element for each equivalence class
		 */
		final UnionFind<CongruenceClosure<NODE>> uf = new UnionFind<>();
		for (final CongruenceClosure<NODE> cc : filteredForWeaker) {
			uf.findAndConstructEquivalenceClassIfNeeded(cc);
		}
		boolean goOn = true;
		while (goOn) {
			goOn = false;
			final Collection<CongruenceClosure<NODE>> repCopy = uf.getAllRepresentatives();
			// TODO optimize
			for (final Entry<CongruenceClosure<NODE>, CongruenceClosure<NODE>> repPair
					: CrossProducts.binarySelectiveCrossProduct(repCopy, false, false).entrySet()) {
				if (mCcComparator.compare(repPair.getKey(), repPair.getValue()) == ComparisonResult.EQUAL) {
					uf.union(repPair.getKey(), repPair.getValue());
					goOn = true;
				}
			}
		}

		final List<CongruenceClosure<NODE>> result = new ArrayList<>(uf.getAllRepresentatives());

		return result;
	}

	public CongruenceClosure<NODE> getSingleDisequalityCc(final NODE elem1, final NODE elem2) {
		final CongruenceClosure<NODE> newCC = new CongruenceClosure<>();
		newCC.reportDisequality(elem1, elem2);
		return newCC;
	}

	public CongruenceClosure<NODE> makeCopy(final CongruenceClosure<NODE> meet) {
		if (meet.isInconsistent()) {
			return meet;
		}
		return new CongruenceClosure<>(meet);
	}

	public CongruenceClosure<NODE> getSingleEqualityCc(final NODE elem1,
			final NODE  elem2) {
		final CongruenceClosure<NODE> newCC = new CongruenceClosure<>();
		newCC.reportEquality(elem1, elem2);
		return newCC;
	}
}