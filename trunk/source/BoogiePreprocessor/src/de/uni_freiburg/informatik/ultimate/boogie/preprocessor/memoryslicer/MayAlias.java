/*
 * Copyright (C) 2023 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2023 University of Freiburg
 *
 * This file is part of the ULTIMATE BoogiePreprocessor plug-in.
 *
 * The ULTIMATE BoogiePreprocessor plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE BoogiePreprocessor plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE BoogiePreprocessor plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE BoogiePreprocessor plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE BoogiePreprocessor plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.boogie.preprocessor.memoryslicer;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.util.datastructures.UnionFind;

/**
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
public class MayAlias {
	private final UnionFind<AddressStore> mAddressStores;
	private final Map<PointerBase, MemorySegment> mPointerBaseToMemorySegment;

	public MayAlias() {
		mAddressStores = new UnionFind<>();
		mPointerBaseToMemorySegment = new HashMap<>();
	}

	public MayAlias(final UnionFind<AddressStore> pointerBases,
			final Map<PointerBase, MemorySegment> pointerBaseToMemorySegment) {
		super();
		mAddressStores = pointerBases;
		mPointerBaseToMemorySegment = pointerBaseToMemorySegment;
	}

//	public MayAlias join(final MayAlias other) {
//		final Map<PointerBase, MemorySegment> newPointerBaseToMemorySegment = new HashMap<>(
//				mPointerBaseToMemorySegment);
//		newPointerBaseToMemorySegment.putAll(other.getPointerBaseToMemorySegment());
//		final UnionFind<AddressStore> newAddressStores = UnionFind.unionPartitionBlocks(mAddressStores,
//				other.getAddressStores());
//		// TODO apply Congruence
////		for (final Set<AddressStore> eq : newAddressStores.getAllEquivalenceClasses()) {
////			appl
////		}
//		return new MayAlias(newAddressStores, newPointerBaseToMemorySegment);
//	}

	public void reportEquivalence(final AddressStoreFactory asFac, final AddressStore lhs, final AddressStore rhs) {
		if ((lhs instanceof PointerBase) && AliasAnalysis.isNullPointer((PointerBase) lhs)) {
			throw new MemorySliceException("Must not add nullpointer");
		}
		if ((rhs instanceof PointerBase) && AliasAnalysis.isNullPointer((PointerBase) rhs)) {
			throw new MemorySliceException("Must not add nullpointer");
		}
		final AddressStore rhsRep = mAddressStores.find(rhs);
		final AddressStore lhsRep = mAddressStores.find(lhs);
		if (rhsRep == lhsRep && rhsRep != null) {
			return;
		}
		if (rhsRep == null) {
			mAddressStores.makeEquivalenceClass(rhs);
			if (rhs instanceof PointerBase) {
				final MemorySegment ms = asFac.getMemorySegment((PointerBase) rhs);
				mPointerBaseToMemorySegment.put((PointerBase) rhs, ms);
				final AddressStore rhsMsRep = mAddressStores.find(ms);
				if (rhsMsRep == null) {
					mAddressStores.makeEquivalenceClass(ms);
				}
			}
		}
		if (lhsRep == null) {
			mAddressStores.makeEquivalenceClass(lhs);
			if (lhs instanceof PointerBase) {
				final MemorySegment ms = asFac.getMemorySegment((PointerBase) lhs);
				mPointerBaseToMemorySegment.put((PointerBase) lhs, ms);
				final AddressStore lhsMsRep = mAddressStores.find(ms);
				if (lhsMsRep == null) {
					mAddressStores.makeEquivalenceClass(ms);
				}
			}
		}
		mAddressStores.union(lhs, rhs);
		{
			final AddressStore rep = mAddressStores.find(lhs);
			applyCongruenceExhaustively(asFac, mAddressStores, rep);
		}
	}

	private void applyCongruenceExhaustively(final AddressStoreFactory asFac, final UnionFind<AddressStore> resultUf,
			final AddressStore someElement) {
		while (true) {
			final Set<AddressStore> equivalenceClass = mAddressStores.getEquivalenceClassMembers(someElement);
			final boolean someModification = applyCongruence(asFac, resultUf, equivalenceClass);
			if (!someModification) {
				return;
			}
		}


	}

	private boolean applyCongruence(final AddressStoreFactory asFac, final UnionFind<AddressStore> resultUf,
			final Set<AddressStore> newEquivalenceClass) {
		// filter PointerBases
		final List<PointerBase> pointerBases = new ArrayList<>();
		for (final AddressStore mem : newEquivalenceClass) {
			if (mem instanceof PointerBase) {
				pointerBases.add((PointerBase) mem);
			}
		}
		// merge equivalence classes of corresponding memory segments
		boolean someModification = false;
		if (!pointerBases.isEmpty()) {
			final MemorySegment ms0 = asFac.getMemorySegment(pointerBases.get(0));
			for (int i = 1; i < pointerBases.size(); i++) {
				final MemorySegment ms = asFac.getMemorySegment(pointerBases.get(i));
				someModification |= resultUf.union(ms0, ms);
			}
		}
		return someModification;
	}

	public void addPointerBase(final AddressStoreFactory asFac, final PointerBase pb) {
		if (AliasAnalysis.isNullPointer(pb)) {
			throw new MemorySliceException("Must not add nullpointer");
		}
		final AddressStore rep = mAddressStores.find(pb);
		final MemorySegment ms = asFac.getMemorySegment(pb);
		final AddressStore msRep = mAddressStores.find(ms);
		if (rep != null && msRep != null) {
			// nothing new was added
			return;
		} else {
			mPointerBaseToMemorySegment.put(pb, ms);
			if (rep == null) {
				mAddressStores.makeEquivalenceClass(pb);
			}
			if (msRep == null) {
				mAddressStores.makeEquivalenceClass(ms);
			}
		}
	}

	public UnionFind<AddressStore> getAddressStores() {
		return mAddressStores;
	}

	public Map<PointerBase, MemorySegment> getPointerBaseToMemorySegment() {
		return mPointerBaseToMemorySegment;
	}

	@Override
	public String toString() {
		return mAddressStores.toString();
	}

}