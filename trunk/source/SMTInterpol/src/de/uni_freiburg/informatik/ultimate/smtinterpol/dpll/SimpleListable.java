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
	SimpleListable<E> mNext;
	SimpleListable<E> mPrev;
	
	/**
	 * Create an element that is not part of any list.
	 */
	public SimpleListable() {
		// Element in no list.
	}

	SimpleListable(SimpleListable<E> next, SimpleListable<E> prev) {
		this.mNext = next;
		this.mPrev = prev;
	}
	
	@SuppressWarnings("unchecked")
	public final E getElem() {
		return (E) this;
	}
	
	public final void removeFromList() {
		mPrev.mNext = mNext;
		mNext.mPrev = mPrev;
		mNext = mPrev = null;
	}

	public final void unlink() {
		mPrev.mNext = mNext;
		mNext.mPrev = mPrev;
	}

	public final void relink() {
		mNext = mPrev.mNext;
		mPrev.mNext = this;
		mNext.mPrev = this;
	}

	public boolean inList() {
		return mNext != null;
	}
}
