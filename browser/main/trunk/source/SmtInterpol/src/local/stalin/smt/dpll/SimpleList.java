package local.stalin.smt.dpll;

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
	
	public void append(E entry) {
		entry.next = this;
		entry.prev = prev;
		this.prev = prev.next = entry;
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
	
	/**
	 * Swap lists that were joined, so that they are joined in the other
	 * direction.  This is equivalent to the two calls:
	 * <pre>this.unjoinList(source);
	 * source.joinList(this)</pre>
	 * although the order of elements is different and it is more efficient.
	 * @param source the list to swap with.  This must be the source in
	 * a previous joinList operation, or the caller of the previous swapList
	 * operation.
	 */
	public void swapList(SimpleList<E> source) {
		/* Nothing to do if the big list was empty */
		if (next == this)
			return;
		this.unjoinList(source);
		source.joinList(this);
		/* TODO : This is broken 
		SimpleListEntry<E> tnext = source.prev.next; 
		SimpleListEntry<E> tprev = source.next.prev;
		source.next = this.next;
		source.prev = this.prev;
		source.next.prev = source;
		source.prev.next = source;
		if (tnext != source) {
			this.next = tnext;
			this.prev = tprev;
		}
		*/
	}
	
	public Iterator<E> iterator() {
		return new Iterator<E>() {
			SimpleListable<E> cur = SimpleList.this.next;
			public boolean hasNext() {
				return cur != SimpleList.this;
			}
			public E next() {
				E data = cur.getElem();
				cur = cur.next;
				return data;
			}
			public void remove() {
				cur.prev = cur.prev.prev;
				cur.prev.next = cur;
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
		if (next.prev != this)
			return false;
		SimpleListable<E> entry = next;
		while (!(entry instanceof SimpleList)) {
			if (entry.next.prev != entry)
				return false;
			entry = entry.next;
		}
		return entry == this;
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
}