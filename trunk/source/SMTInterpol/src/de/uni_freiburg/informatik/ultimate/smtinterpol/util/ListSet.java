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
import java.util.HashSet;
import java.util.Iterator;

/**
 * A scoped combination of a set and a list.  Elements are unique within this
 * collection (as in sets) and can be iterated in an order (as in lists).
 * 
 * Whenever a new scope is created, an empty list element is inserted into the
 * list (not into the set) and marks the beginning of this scope.  The scope is
 * invisible for <code>ListSetIterator</code>, be can be retrieved using
 * <code>ScopeIterator</code>.  Note that scope iterators traverse only the top
 * most scope and in the opposite order of the input.
 * @author Juergen Christ
 */
public class ListSet<E> extends AbstractSet<E> {
	
	private class ScopeIterator implements Iterator<E> {
		ListSetElem<E> mCur = mRoot;
		@Override
		public boolean hasNext() {
			return mCur.mPrev.mElem != null;
		}

		@Override
		public E next() {
			mCur = mCur.mPrev;
			return mCur.mElem;
		}

		@Override
		public void remove() {
			mCur = ListSet.this.remove(mCur).mNext;
			ListSet.this.mElems.remove(mCur);
		}
		
	}
	
	public class ListSetIterator implements Iterator<E> {

		ListSetElem<E> mCur;
		
		ListSetIterator(ListSetElem<E> cur) {
			mCur = cur;
		}
		
		@Override
		public boolean hasNext() {
			ListSetElem<E> walk = mCur.mNext;
			while (walk != mRoot && walk.mElem == null) {
				walk = walk.mNext;
			}
			return walk != mRoot;
		}

		@Override
		public E next() {
			ListSetElem<E> walk = mCur.mNext;
			while (walk != mRoot && walk.mElem == null) {
				walk = walk.mNext;
			}
			mCur = walk;
			return mCur.mElem;
		}

		@Override
		public void remove() {
			mCur = ListSet.this.remove(mCur);
			ListSet.this.mElems.remove(mCur);
		}
		
	}
	
	private static class ListSetElem<E> {
		E mElem;
		ListSetElem<E> mNext;
		ListSetElem<E> mPrev;
		public ListSetElem(E elem) {
			this.mElem = elem;
			mNext = mPrev = this;
		}
		@Override
		public int hashCode() {
			return mElem == null ? 0 : mElem.hashCode();
		}
		@Override
		public boolean equals(Object other) {
			if (other instanceof ListSetElem<?>) {
				other = ((ListSetElem<?>)other).mElem;
			}
			return mElem == null ? other == null : mElem.equals(other);
		}
	}
	
	private final HashSet<ListSetElem<E>> mElems;
	private final ListSetElem<E> mRoot;
	
	public ListSet() {
		mElems = new HashSet<ListSetElem<E>>();
		mRoot = new ListSetElem<E>(null);
	}
	
	public void beginScope() {
		final ListSetElem<E> marker = new ListSetElem<E>(null);
		addToList(marker);
	}
	
	public void endScope() {
		ListSetElem<E> walk = mRoot.mPrev;
		while (walk.mElem != null) {
			mElems.remove(walk);
			walk = remove(walk);
		}
	}
	
	private void addToList(ListSetElem<E> toAdd) {
		mRoot.mPrev.mNext = toAdd;
		toAdd.mNext = mRoot;
		toAdd.mPrev = mRoot.mPrev;
		mRoot.mPrev = toAdd;
	}
	
	@Override
	public boolean add(E elem) {
		final ListSetElem<E> toAdd = new ListSetElem<E>(elem);
		if (mElems.add(toAdd)) {
			addToList(toAdd);
			return true;
		}
		return false;
	}

	// This iterator is not concurrent...
	@Override
	public Iterator<E> iterator() {
		return new Iterator<E>() {

			Iterator<ListSetElem<E>> mIt = mElems.iterator();
			ListSetElem<E> mData;
			
			@Override
			public boolean hasNext() {
				return mIt.hasNext();
			}

			@Override
			public E next() {
				return (mData = mIt.next()).mElem;
			}

			@Override
			public void remove() {
				ListSet.this.remove(mData);
				mIt.remove();
			}
			
		};
	}
	
	private ListSetElem<E> remove(ListSetElem<E> elem) {
		final ListSetElem<E> prev = elem.mPrev;
		prev.mNext = elem.mNext;
		elem.mNext.mPrev = prev;
		elem.mNext = elem.mPrev = elem;
		// Don't do that since this method is called from the iterator
//		m_elems.remove(elem);
		return prev;
	}

	@Override
	public int size() {
		return mElems.size();
	}
	
	public ListSetIterator listIterator() {
		return new ListSetIterator(mRoot);
	}
	
	public ListSetIterator successors(ListSetIterator it) {
		return new ListSetIterator(it.mCur);
	}
	
	public Iterator<E> scopeIterator() {
		return new ScopeIterator();
	}
	
	public Iterable<E> scope() {
		return new Iterable<E>() {

			@Override
			public Iterator<E> iterator() {
				return scopeIterator();
			}
			
		};
	}

}
