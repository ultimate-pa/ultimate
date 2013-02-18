package local.stalin.smt.dpll;

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
 * @author hoenicke
 *
 */
public class SimpleListable<E extends SimpleListable<E>> {
	SimpleListable<E> next;
	SimpleListable<E> prev;
	
	public SimpleListable() {
	}

	SimpleListable(SimpleListable<E> next, SimpleListable<E> prev) {
		this.next = next;
		this.prev = prev;
	}
	
	@SuppressWarnings("unchecked")
	public final E getElem() {
		return (E) this;
	}
	
	public final void removeFromList() {
		prev.next = next;
		next.prev = prev;
		next = prev = null;
	}

	public final void unlink() {
		prev.next = next;
		next.prev = prev;
	}

	public final void relink() {
		prev.next = this;
		next.prev = this;
	}
}