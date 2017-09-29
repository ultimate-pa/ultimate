package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.states;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.Map.Entry;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.IEqNodeIdentifier;
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
//		final List<CongruenceClosure<NODE>> filteredForWeaker = new ArrayList<>();

//		/*
//		 * filter strictly weaker elements
//		 */
//		for (final CongruenceClosure<NODE> cc1 : unionList) {
//			boolean foundStrictlyWeakerElement = false;
//			for (final CongruenceClosure<NODE> cc2 : unionList) {
//				if (!cc2.isStrongerThan(cc1)) {
//					/*
//					 * ! cc2 <= cc1  <-> cc1 < cc2
//					 * drop cc1 as there is a strictly weaker element
//					 */
//					foundStrictlyWeakerElement = true;
//					break;
//				}
//			}
//			if (!foundStrictlyWeakerElement) {
//				filteredForWeaker.add(cc1);
//			}
//		}
//

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
//				if (repPair.getKey().isEquivalent(repPair.getValue())) {
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