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
package de.uni_freiburg.informatik.ultimate.boogie.preprocessor.heapsplitter;

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

	public MayAlias join(final MayAlias other) {
		final Map<PointerBase, MemorySegment> newPointerBaseToMemorySegment = new HashMap<>(
				mPointerBaseToMemorySegment);
		newPointerBaseToMemorySegment.putAll(other.getPointerBaseToMemorySegment());
		final UnionFind<AddressStore> newAddressStores = UnionFind.unionPartitionBlocks(mAddressStores,
				other.getAddressStores());
		// TODO apply Congruence
//		for (final Set<AddressStore> eq : newAddressStores.getAllEquivalenceClasses()) {
//			appl
//		}
		return new MayAlias(newAddressStores, newPointerBaseToMemorySegment);
	}

	public MayAlias reportEquivalence(final AddressStoreFactory asFac, final AddressStore lhs, final AddressStore rhs) {
		final AddressStore rhsRep = mAddressStores.find(rhs);
		final AddressStore lhsRep = mAddressStores.find(lhs);
		if (rhsRep == lhsRep && rhsRep != null) {
			return new MayAlias(mAddressStores, mPointerBaseToMemorySegment);
		}
		final UnionFind<AddressStore> resultUf = mAddressStores.clone();
		final Map<PointerBase, MemorySegment> newPointerBaseToMemorySegment = new HashMap<>(
				mPointerBaseToMemorySegment);
		if (rhsRep == null) {
			resultUf.makeEquivalenceClass(rhs);
			if (rhs instanceof PointerBase) {
				final MemorySegment ms = asFac.getMemorySegment((PointerBase) rhs);
				newPointerBaseToMemorySegment.put((PointerBase) rhs, ms);
				final AddressStore rhsMsRep = resultUf.find(ms);
				if (rhsMsRep == null) {
					resultUf.makeEquivalenceClass(ms);
				}
			}
		}
		if (lhsRep == null) {
			resultUf.makeEquivalenceClass(lhs);
			if (lhs instanceof PointerBase) {
				final MemorySegment ms = asFac.getMemorySegment((PointerBase) lhs);
				newPointerBaseToMemorySegment.put((PointerBase) lhs, ms);
				final AddressStore lhsMsRep = resultUf.find(ms);
				if (lhsMsRep == null) {
					resultUf.makeEquivalenceClass(ms);
				}
			}
		}
		resultUf.union(lhs, rhs);
		{
			final AddressStore rep = resultUf.find(lhs);
			final Set<AddressStore> newEquivalenceClass = resultUf.getEquivalenceClassMembers(rep);
			// TODO: apply congruence repeatedly
			applyCongruence(asFac, resultUf, newEquivalenceClass);
		}
		return new MayAlias(resultUf, newPointerBaseToMemorySegment);
	}

	private void applyCongruence(final AddressStoreFactory asFac, final UnionFind<AddressStore> resultUf,
			final Set<AddressStore> newEquivalenceClass) {
		final List<PointerBase> pointerBases = new ArrayList<>();
		for (final AddressStore mem : newEquivalenceClass) {
			if (mem instanceof PointerBase) {
				pointerBases.add((PointerBase) mem);
			}
		}
		if (!pointerBases.isEmpty()) {
			final MemorySegment ms0 = asFac.getMemorySegment(pointerBases.get(0));
			for (int i = 1; i < pointerBases.size(); i++) {
				final MemorySegment ms = asFac.getMemorySegment(pointerBases.get(i));
				resultUf.union(ms0, ms);
			}
		}
	}

	public MayAlias addPointerBase(final AddressStoreFactory asFac, final PointerBase pb) {
		final AddressStore rep = mAddressStores.find(pb);
		final MemorySegment ms = asFac.getMemorySegment(pb);
		final AddressStore msRep = mAddressStores.find(ms);
		if (rep != null && msRep != null) {
			// nothing new was added
			return this;
		} else {
			final UnionFind<AddressStore> newuf = mAddressStores.clone();
			final Map<PointerBase, MemorySegment> newPointerBaseToMemorySegment = new HashMap<>(
					mPointerBaseToMemorySegment);
			newPointerBaseToMemorySegment.put(pb, ms);
			if (rep == null) {
				newuf.makeEquivalenceClass(pb);
			}
			if (msRep == null) {
				newuf.makeEquivalenceClass(ms);
			}
			return new MayAlias(newuf, newPointerBaseToMemorySegment);
		}
	}

	private UnionFind<AddressStore> getAddressStores() {
		return mAddressStores;
	}

	public Map<PointerBase, MemorySegment> getPointerBaseToMemorySegment() {
		return mPointerBaseToMemorySegment;
	}

	@Override
	public String toString() {
		return mAddressStores.toString();
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((mAddressStores == null) ? 0 : mAddressStores.hashCode());
		return result;
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		}
		if (obj == null) {
			return false;
		}
		if (getClass() != obj.getClass()) {
			return false;
		}
		final MayAlias other = (MayAlias) obj;
		if (mAddressStores == null) {
			if (other.mAddressStores != null) {
				return false;
			}
		} else if (!mAddressStores.equals(other.mAddressStores)) {
			return false;
		}
		return true;
	}

}