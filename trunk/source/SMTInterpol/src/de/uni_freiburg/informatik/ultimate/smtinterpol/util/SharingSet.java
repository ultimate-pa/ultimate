/*
 * Copyright (C) 2009-2012 University of Freiburg
 *
 * This file is part of SMTInterpol.
 *
 * SMTInterpol is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * SMTInterpol is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with SMTInterpol.  If not, see <http://www.gnu.org/licenses/>.
 */
package de.uni_freiburg.informatik.ultimate.smtinterpol.util;

import java.util.AbstractSet;
import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Set;

public class SharingSet<E> extends AbstractSet<E> {
	
	private static final class SharingSetData<E> {
		SharingSetData() {
			mRep = new HashSet<E>();
			mSharing = 0;
		}
		SharingSetData(SharingSetData<E> other) {
			mRep = new HashSet<E>(other.mRep);
			mSharing = 0;
		}
		SharingSetData(E obj) {
			mRep = Collections.singleton(obj);
			// HACK: The first write modification has to copy the map since it
			//       is immutable...
			mSharing = 1;
		}
		Set<E> mRep;
		// XXX Should this be atomic for multi threading support
		// Currently, we do not support multiple threads!!!
		int mSharing;
		SharingSetData<E> share() {
			++mSharing;
			return this;
		}
		SharingSetData<E> detach() {
			if (mSharing != 0) {
				// one shared access less
				--mSharing;
				return new SharingSetData<E>(this);
			}
			return this;
		}
	}
	
	private SharingSetData<E> mData;
	
	public SharingSet() {
		mData = new SharingSetData<E>();
	}
	
	public SharingSet(SharingSet<E> other) {
		mData = other.mData.share();
	}
	// UNMODIFIABLE sharing set...
	public SharingSet(E obj) {
		mData = new SharingSetData<E>(obj);
	}

	@Override
	public Iterator<E> iterator() {
		return new Iterator<E>() {
			Iterator<E> mSink = mData.mRep.iterator();
			@Override
			public boolean hasNext() {
				return mSink.hasNext();
			}

			@Override
			public E next() {
				return mSink.next();
			}

			@Override
			public void remove() {
				throw new UnsupportedOperationException(
						"remove not allowed on SharingSet iterator");
			}
			
		};
	}

	@Override
	public int size() {
		return mData.mRep.size();
	}

	@Override
	public boolean removeAll(Collection<?> c) {
		final SharingSetData<E> data = mData.detach();
		final boolean res = data.mRep.removeAll(c);
		if (res) {
			mData = data;
		}
		return res;
	}

	@Override
	public boolean add(E e) {
		if (mData.mRep.contains(e)) {
			return false;
		}
		mData = mData.detach();
		return mData.mRep.add(e);
	}

	@Override
	public boolean addAll(Collection<? extends E> c) {
		if (mData.mRep.containsAll(c)) {
			return false;
		}
		mData = mData.detach();
		return mData.mRep.addAll(c);
	}
	// Optimization for sharing sets...
	public boolean addShared(SharingSet<E> other) {
		if (other == null) {
			return false;
		}
		if (mData.mRep.isEmpty() && mData.mSharing == 0) {
			mData = other.mData.share();
			return true;
		}
		return addAll(other.mData.mRep);
	}

	@Override
	public boolean contains(Object o) {
		return mData.mRep.contains(o);
	}

	@Override
	public boolean containsAll(Collection<?> c) {
		return mData.mRep.containsAll(c);
	}

	@Override
	public boolean remove(Object o) {
		if (mData.mRep.contains(o)) {
			mData = mData.detach();
			return mData.mRep.remove(o);
		}
		return false;
	}

}
