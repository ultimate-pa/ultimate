package de.uni_freiburg.informatik.ultimate.util.datastructures.poset;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.util.datastructures.UnionFind;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

public class PartialOrderCache<E> {

	private final IPartialComparator<E> mComparator;

	private final HashRelation<E, E> mStrictlySmaller;
	private final UnionFind<E> mEquivalences;

	private final Set<E> mMaximalElements;
	private final Set<E> mMinimalElements;



	public PartialOrderCache(final IPartialComparator<E> comparator) {
		mComparator = comparator;
		mStrictlySmaller = new HashRelation<>();
		mEquivalences = new UnionFind<>();
		mMaximalElements = new HashSet<>();
		mMinimalElements = new HashSet<>();
	}

	public E addElement(final E elemToAdd) {
		E rep = mEquivalences.find(elemToAdd);
		if (rep != null) {
			// we already know this element, return the representative
			return rep;
		}
		// elemToAdd element is new
		rep = mEquivalences.findAndConstructEquivalenceClassIfNeeded(elemToAdd);
		assert rep == elemToAdd;
		mMinimalElements.add(rep);
		mMaximalElements.add(rep);

		for (final E otherRep : new ArrayList<>(mEquivalences.getAllRepresentatives())) {
			if (otherRep == rep) {
				// nothing to do
				continue;
			}
			switch (mComparator.compare(elemToAdd, otherRep)) {
			case EQUAL:
				mEquivalences.union(rep, otherRep);
				final E newRep = mEquivalences.find(rep);
				if (newRep == rep) {
					// representative has changed
					assert mEquivalences.find(otherRep) == rep;
					mMinimalElements.remove(otherRep);
					mMaximalElements.remove(otherRep);
					mStrictlySmaller.replaceDomainElement(otherRep, newRep);
					mStrictlySmaller.replaceRangeElement(otherRep, newRep);
				} else {
					// representative is the old one but we have already made some entries into the data structures
					mMinimalElements.remove(rep);
					mMaximalElements.remove(rep);
					mStrictlySmaller.replaceDomainElement(rep, newRep);
					mStrictlySmaller.replaceRangeElement(rep, newRep);
				}
				assert sanityCheck();
				return newRep;
			case STRICTLY_SMALLER:
				addStrictlySmaller(elemToAdd, otherRep);
				break;
			case STRICTLY_GREATER:
				addStrictlySmaller(otherRep, elemToAdd);
				break;
			case INCOMPARABLE:
				break;
			}
		}

		assert sanityCheck();
		return rep;
	}

	private void addStrictlySmaller(final E smaller, final E greater) {
		assert mEquivalences.find(smaller) == smaller;
		assert mEquivalences.find(greater) == greater;

		final E smallerRep = mEquivalences.find(smaller);
		final E greaterRep = mEquivalences.find(greater);

		mStrictlySmaller.addPair(smallerRep, greaterRep);
//		mExplies.addPair(greaterRep, smallerRep);

		mMinimalElements.remove(greaterRep);
		mMaximalElements.remove(smallerRep);

		assert sanityCheck();
	}

	public boolean lowerEqual(final E elem1, final E elem2) {
		throw new UnsupportedOperationException("not yet implemented");
	}

	public boolean greaterEqual(final E elem1, final E elem2) {
		throw new UnsupportedOperationException("not yet implemented");
	}

	public Set<E> getMaximalRepresentatives() {
		return mMaximalElements;
	}

	public Set<E> getMinimalRepresentatives() {
		return mMinimalElements;
	}



	boolean sanityCheck() {
		/*
		 * the sets mMinimalElemnts and mMaximalElements may only contain representatives
		 */
		for (final E e : mMinimalElements) {
			if (mEquivalences.find(e) != e) {
				final E find = mEquivalences.find(e);
				assert false;
				return false;
			}
		}
		for (final E e : mMaximalElements) {
			if (mEquivalences.find(e) != e) {
				final E find = mEquivalences.find(e);
				assert false;
				return false;
			}
		}

		for (final Entry<E, E> en : mStrictlySmaller) {
			if (mEquivalences.find(en.getKey()) != en.getKey()) {
				final E find = mEquivalences.find(en.getKey());
				assert false;
				return false;
			}
			if (mEquivalences.find(en.getValue()) != en.getValue()) {
				final E find = mEquivalences.find(en.getValue());
				assert false;
				return false;
			}
		}


		return true;
	}

}
