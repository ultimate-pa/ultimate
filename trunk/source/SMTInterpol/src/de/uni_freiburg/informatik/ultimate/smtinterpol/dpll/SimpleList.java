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
package de.uni_freiburg.informatik.ultimate.smtinterpol.dpll;

import java.util.Iterator;

/**
 * A light-weight double linked list entry.  The usage is a bit complicated but  
 * it gives better performance than LinkedList.  To use this class define
 * a class <code>foo</code> of things you want to keep in a linked list
 * and extend it from <code>SimpleListable&lt;foo&gt;.
 * You can then append it to a <code>SimpleList&lt;foo&gt;.
 * 
 * <em>Note:</em> 
 * <ul><li>Every element of <code>foo</code> can only be in one list.  This is because
 * the back/front pointers are in the object.</li>
 * <li>Since you need to extend the class SimpleListable, the class cannot extend another
 * class</li>
 * <li>If you want to store a class <code>elem</code> that does not meet the above 
 * requirements, write a class <code>wrapper</code> that extends 
 * <code>SimpleListable&lt;wrapper&gt;</code> with a field <code>elem</code>.
 * This has a performance similar to <code>LinkedList</code>.</li>
 * </ul>
 * 
 * For technical reasons SimpleList it extends SimpleListable, but you must not
 * use any of its methods.
 * 
 * @author hoenicke
 *
 */
public class SimpleList<E extends SimpleListable<E>> extends SimpleListable<E>
    implements Iterable<E> {
	public SimpleList() {
		mNext = mPrev = this;
	}
	
	public boolean isEmpty() {
		return mNext == this;
	}
	
	public E removeFirst() {
		final SimpleListable<E> entry = mNext;
		mNext = entry.mNext;
		mNext.mPrev = this;
		entry.mNext = entry.mPrev = null;
		return entry.getElem();			
	}
	
	public E removeLast() {
		final SimpleListable<E> entry = mPrev;
		mPrev = entry.mPrev;
		mPrev.mNext = this;
		entry.mNext = entry.mPrev = null;
		return entry.getElem();			
	}
	
	/**
	 * Prepares to remove an entry from joined lists.  Call this on all lists
	 * the entry has been joined into starting from the innermost one.
	 * Afterwards, call <code>entry.removeFromList()</code>.  
	 * @param entry Entry to remove.
	 */
	public void prepareRemove(E entry) {
		if (mNext == entry) {
			if (mPrev == entry) {
				mNext = mPrev = this;
			} else {
				mNext = entry.mNext;
			}
		} else if (mPrev == entry) {
			mPrev = entry.mPrev;
		}
	}
	
	/**
	 * Append an entry to the end of the list.  
	 */
	public void append(E entry) {
		assert (mPrev.mNext == this);
		entry.mPrev = mPrev;
		entry.mNext = this;
		mPrev = mPrev.mNext = entry;
	}

	/**
	 * Prepend an entry to the beginning of the list.   
	 * @param entry the element to prepend.
	 */
	public void prepend(E entry) {
		assert (mNext.mPrev == this);
		entry.mNext = mNext;
		entry.mPrev = this;
		mNext.mPrev = entry;
		mNext = entry;
	}

	/**
	 * Prepend an entry to the beginning of a joined list.  This must also
	 * be called on all lists to which this list was joined to.  The entry
	 * must have been fresh, i.e. next and prev pointers must be null.
	 * The entry must first be added to the inner-most list and then to all
	 * lists, for which joinList was executed on the list. 
	 * @param entry the element to prepend.
	 */
	public void prependIntoJoined(E entry, boolean isLast) {
		if (entry.mNext == null) {
			if (this != mNext || isLast) { // NOPMD
				/* only if list is not empty or in the last step, 
				 * we can set entry.next */
				entry.mNext = mNext;
				entry.mPrev = mNext.mPrev;
				if (mNext.mPrev != this) {
					mNext.mPrev.mNext = entry;
				}
			}
			/* link entry into the list */
			mNext.mPrev = entry;
			mNext = entry;
		} else {
			/* The entry was already added in a previous call to a non-empty
			 * list.  Since the remaining lists have been joined with the list,
			 * they contain the element entry.next.  
			 * We already changed entry.next.prev to insert entry to the list
			 * so entry is already added to all lists that contain also 
			 * entry.next.prev.  However, if the list starts with entry.next
			 * we still have to add entry to the list.
			 */
			if (mNext == entry.mNext) {
				mNext = entry;
			}
		}
	}

	/**
	 * Move all elements from source list to the end of this list.
	 * @param source the source list.
	 */
	public void moveAll(SimpleList<E> source) {
		/* If source is empty this is a no-op */
		if (source.mNext == source) {
			return;
		}
		source.mNext.mPrev = mPrev;
		source.mPrev.mNext = this;
		mPrev.mNext = source.mNext;
		mPrev = source.mPrev;
		source.mNext = source.mPrev = source;
	}
	
	/**
	 * Move the elements from source to this list, but do not clear source.
	 * This operation can be undone unjoinLists.  However, source must not
	 * be touched in between.  It is allowed to add new elements to this, 
	 * though, as long as they are not added to the middle.
	 * @param source the source list which is joined into this list.
	 */
	public void joinList(SimpleList<E> source) {
		/* If source is empty this is a no-op */
		if (source.mNext == source) {
			return;
		}
		/* Otherwise concatenate the lists.
		 * Do not change the source list head, so that unjoin works. */
		mPrev.mNext = source.mNext;
		source.mNext.mPrev = mPrev;
		mPrev = source.mPrev;
		mPrev.mNext = this;
	}
	
	/**
	 * Undo the join of this and source.  This moves the elements from this
	 * back to source that were in source before.  It is essential that
	 * source was not touched in between.
	 * @param source the source list which is joined into this list.
	 */
	public void unjoinList(SimpleList<E> source) {
		/* source.next/source.prev still point to the start and end
		 * of the source list.
		 */
		// Unlink source list from this list.
		source.mPrev.mNext.mPrev = source.mNext.mPrev;
		source.mNext.mPrev.mNext = source.mPrev.mNext;
		// And link it to source.
		source.mNext.mPrev = source;
		source.mPrev.mNext = source;
	}
	
	@Override
	public Iterator<E> iterator() {
		return new Iterator<E>() {
			SimpleListable<E> mCur = SimpleList.this;
			SimpleListable<E> mPrev = null;
			@Override
			public boolean hasNext() {
				return mCur != SimpleList.this.mPrev;
			}
			@Override
			public E next() {
				mPrev = mCur;
				mCur = mCur.mNext;
				return mCur.getElem();
			}
			@Override
			public void remove() {
				assert (mPrev != null);
				mPrev.mNext = mCur.mNext;
				mCur.mNext.mPrev = mPrev;
				mCur.mNext = null;
				mCur.mPrev = null;
				mCur = mPrev;
				mPrev = null;
			}
		};
	}

	public Iterable<E> reverse() {
		return new Iterable<E>() {
			@Override
			public Iterator<E> iterator() {
				return new Iterator<E>() {
					SimpleListable<E> mCur = SimpleList.this.mPrev;
					@Override
					public boolean hasNext() {
						return mCur != SimpleList.this;
					}
					@Override
					public E next() {
						final E data = mCur.getElem();
						mCur = mCur.mPrev;
						return data;
					}
					@Override
					public void remove() {
						mCur.mNext = mCur.mNext.mNext;
						mCur.mNext.mPrev = mCur;
					}
				};
			}
		};
	}
	
	/**
	 * Remove all elements from this list.
	 */
	public void clear() {
		mNext = mPrev = this;
	}
	
	public boolean wellformed() {
		if (mNext.mPrev != this) {
			System.err.println("Not in this list!!!!");
			return false;
		}
		SimpleListable<E> entry = mNext;
		while (!(entry instanceof SimpleList<?>)) {
			if (entry.mNext.mPrev != entry) {
				System.err.println("Wrong links!!!!");
				return false;
			}
			entry = entry.mNext;
		}
		return entry == this;
	}

	public boolean wellformedPart() {
		SimpleListable<E> entry = mNext;
		while (entry != mPrev) {
			if (entry instanceof SimpleList<?>) {
				return false;
			}
			if (entry.mNext.mPrev != entry) {
				return false;
			}
			entry = entry.mNext;
		}
		return true;
	}
	
	public boolean contains(E elem) {
		SimpleListable<E> entry = mNext;
		while (entry != this) {
			if (entry.getElem().equals(elem)) {
				return true;
			}
			entry = entry.mNext;
		}
		return false;
	}
	
	@Override
	public String toString() {
		if (mNext == this) {
			return "[]";
		}
		final StringBuilder sb = new StringBuilder();
		if (mNext.mPrev != this) {
			sb.append('~');
		}
		sb.append('[');
		SimpleListable<E> entry;
		for (entry = mNext; entry != mPrev; entry = entry.mNext) {
			sb.append(entry).append(",");
		}
		sb.append(entry);
		sb.append(']');
		return sb.toString();
	}

	public SimpleList<E> cloneJoinedList() {
		final SimpleList<E> clonedList = new SimpleList<E>();
		clonedList.mNext = mNext;
		clonedList.mPrev = mPrev;
		if (mNext.mPrev == this) {
			mNext.mPrev = clonedList;
			mPrev.mNext = clonedList;
		}
		return clonedList;
	}
}
