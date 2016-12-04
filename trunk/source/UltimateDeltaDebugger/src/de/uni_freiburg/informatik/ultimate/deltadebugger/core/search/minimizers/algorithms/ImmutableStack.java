/*
 * Copyright (C) 2016 University of Freiburg
 *
 * This file is part of the Ultimate Delta Debugger plug-in.
 *
 * The Ultimate Delta Debugger plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The Ultimate Delta Debugger plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the Ultimate Delta Debugger plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the Ultimate Delta Debugger plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the Ultimate Delta Debugger plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.deltadebugger.core.search.minimizers.algorithms;

import java.util.EmptyStackException;

/**
 * Immutable stack (effectively a singly linked list).
 *
 * @param <E>
 *            element type
 */
public final class ImmutableStack<E> {
	@SuppressWarnings("rawtypes")
	public static final ImmutableStack EMPTY_STACK = new ImmutableStack();
	
	private final E mHead;
	private final ImmutableStack<E> mTail;
	
	private ImmutableStack() {
		mHead = null;
		mTail = this;
	}
	
	private ImmutableStack(final E head, final ImmutableStack<E> tail) {
		mHead = head;
		mTail = tail;
	}
	
	/**
	 * @param <E>
	 *            Element type.
	 * @return empty stack
	 */
	@SuppressWarnings("unchecked")
	public static <E> ImmutableStack<E> emptyStack() {
		return EMPTY_STACK;
	}
	
	/**
	 * @param fifoItems
	 *            Elements in FIFO order.
	 * @param <E>
	 *            element type
	 * @return stack
	 */
	@SafeVarargs
	public static <E> ImmutableStack<E> of(final E... fifoItems) {
		ImmutableStack<E> stack = emptyStack();
		for (int i = fifoItems.length - 1; i >= 0; --i) {
			stack = stack.push(fifoItems[i]);
		}
		return stack;
	}
	
	/**
	 * @return {@code true} iff the stack is empty.
	 */
	public boolean isEmpty() {
		return mTail.equals(this);
	}
	
	/**
	 * @return Top element (retained).
	 */
	public E peek() {
		if (isEmpty()) {
			throw new EmptyStackException();
		}
		return mHead;
	}
	
	/**
	 * @return Top element (removed).
	 */
	public ImmutableStack<E> pop() {
		if (isEmpty()) {
			throw new EmptyStackException();
		}
		return mTail;
	}
	
	/**
	 * @param item
	 *            New element.
	 * @return new stack
	 */
	public ImmutableStack<E> push(final E item) {
		return new ImmutableStack<>(item, this);
	}
	
	/**
	 * @return Stack size in use.
	 */
	public int size() {
		int result = 0;
		for (ImmutableStack<E> stack = this; !stack.isEmpty(); stack = stack.pop()) {
			++result;
		}
		return result;
	}
}
