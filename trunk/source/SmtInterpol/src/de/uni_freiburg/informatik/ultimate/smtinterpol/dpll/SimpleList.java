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
public class SimpleList<E extends SimpleListable<E>> extends SimpleListable<E> implements Iterable<E> {
	public SimpleList() {
		next = prev = this;
	}
	
	public boolean isEmpty() {
		return next == this;
	}
	
	public E removeFirst() {
		SimpleListable<E> entry = next;
		next = entry.next;
		next.prev = this;
		entry.next = entry.prev = null;
		return entry.getElem();			
	}
	
	public E removeLast() {
		SimpleListable<E> entry = prev;
		prev = entry.prev;
		prev.next = this;
		entry.next = entry.prev = null;
		return entry.getElem();			
	}
	
	/**
	 * Prepares to remove an entry from joined lists.  Call this on all lists
	 * the entry has been joined into starting from the innermost one.
	 * Afterwards, call <code>entry.removeFromList()</code>.  
	 * @param entry Entry to remove.
	 */
	public void prepareRemove(E entry) {
		if (next == entry) {
			if (prev == entry)
				next = prev = this;
			else
				next = entry.next;
		} else if (prev == entry)
			prev = entry.prev;
	}
	
	/**
	 * Append an entry to the end of the list.  
	 */
	public void append(E entry) {
		assert (prev.next == this);
		entry.prev = prev;
		entry.next = this;
		this.prev = prev.next = entry;
	}

	/**
	 * Prepend an entry to the beginning of the list.   
	 * @param entry the element to prepend.
	 */
	public void prepend(E entry) {
		assert (next.prev == this);
		entry.next = next;
		entry.prev = this;
		next.prev = entry;
		next = entry;
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
		if (entry.next != null) {
			/* The entry was already added in a previous call to a non-empty
			 * list.  Since the remaining lists have been joined with the list,
			 * they contain the element entry.next.  
			 * We already changed entry.next.prev to insert entry to the list
			 * so entry is already added to all lists that contain also 
			 * entry.next.prev.  However, if the list starts with entry.next
			 * we still have to add entry to the list.
			 */
			if (next == entry.next)
				next = entry;
		} else {
			if (this != next || isLast) {
				/* only if list is not empty or in the last step, 
				 * we can set entry.next */
				entry.next = next;
				entry.prev = next.prev;
				if (next.prev != this)
					next.prev.next = entry;
			}
			/* link entry into the list */
			next.prev = entry;
			next = entry;
		}
	}

	/**
	 * Move all elements from source list to the end of this list.
	 * @param source the source list.
	 */
	public void moveAll(SimpleList<E> source) {
		/* If source is empty this is a no-op */
		if (source.next == source)
			return;
		source.next.prev = this.prev;
		source.prev.next = this;
		this.prev.next = source.next;
		this.prev = source.prev;
		source.next = source.prev = source;
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
		if (source.next == source)
			return;
		/* Otherwise concatenate the lists.
		 * Do not change the source list head, so that unjoin works. */
		prev.next = source.next;
		source.next.prev = prev;
		prev = source.prev;
		prev.next = this;
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
		source.prev.next.prev = source.next.prev;
		source.next.prev.next = source.prev.next;
		// And link it to source.
		source.next.prev = source;
		source.prev.next = source;
	}
	
	public Iterator<E> iterator() {
		return new Iterator<E>() {
			SimpleListable<E> cur = SimpleList.this;
			SimpleListable<E> prev = null;
			public boolean hasNext() {
				return cur != SimpleList.this.prev;
			}
			public E next() {
				prev = cur;
				cur = cur.next;
				return cur.getElem();
			}
			public void remove() {
				assert (prev != null);
				prev.next = cur.next;
				cur.next.prev = prev;
				cur.next = null;
				cur.prev = null;
				cur = prev;
				prev = null;
			}
		};
	}

	public Iterable<E> reverse() {
		return new Iterable<E>() {
			public Iterator<E> iterator() {
				return new Iterator<E>() {
					SimpleListable<E> cur = SimpleList.this.prev;
					public boolean hasNext() {
						return cur != SimpleList.this;
					}
					public E next() {
						E data = cur.getElem();
						cur = cur.prev;
						return data;
					}
					public void remove() {
						cur.next = cur.next.next;
						cur.next.prev = cur;
					}
				};
			}
		};
	}
	
	/**
	 * Remove all elements from this list.
	 */
	public void clear() {
		next = prev = this;
	}
	
	public boolean wellformed() {
		if (next.prev != this) {
			System.err.println("Not in this list!!!!");
			return false;
		}
		SimpleListable<E> entry = next;
		while (!(entry instanceof SimpleList<?>)) {
			if (entry.next.prev != entry) {
				System.err.println("Wrong links!!!!");
				return false;
			}
			entry = entry.next;
		}
		return entry == this;
	}

	public boolean wellformedPart() {
		SimpleListable<E> entry = next;
		while (entry != prev) {
			if (entry instanceof SimpleList<?>)
				return false;
			if (entry.next.prev != entry)
				return false;
			entry = entry.next;
		}
		return true;
	}
	
	public boolean contains(E elem) {
		SimpleListable<E> entry = next;
		while (entry != this) {
			if (entry.getElem().equals(elem))
				return true;
			entry = entry.next;
		}
		return false;
	}
	
	public String toString() {
		if (next == this)
			return "[]";
		StringBuilder sb = new StringBuilder();
		if (next.prev != this)
			sb.append("~");
		sb.append("[");
		SimpleListable<E> entry;
		for (entry = next; entry != prev; entry = entry.next) {
			sb.append(entry).append(",");
		}
		sb.append(entry);
		sb.append("]");
		return sb.toString();
	}

	public SimpleList<E> cloneJoinedList() {
		SimpleList<E> clonedList = new SimpleList<E>();
		clonedList.next = this.next;
		clonedList.prev = this.prev;
		if (this.next.prev == this) {
			this.next.prev = clonedList;
			this.prev.next = clonedList;
		}
		return clonedList;
	}
}
