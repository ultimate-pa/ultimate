package de.uni_freiburg.informatik.ultimate.deltadebugger.core.search.minimizers.algorithms;

import java.util.EmptyStackException;

/**
 * Immutable stack (effectively a singly linked list)
 *
 * @param <E>
 *            element type
 */
public final class ImmutableStack<E> {
	
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
	
	
	public static <T> ImmutableStack<T> emptyStack() {
		return EMPTY_STACK;
	}
	
	@SafeVarargs
	public static <E> ImmutableStack<E> of(final E... fifoItems) {
		ImmutableStack<E> stack = emptyStack();
		for (int i = fifoItems.length - 1; i >= 0; --i) {
			stack = stack.push(fifoItems[i]);
		}
		return stack;
	}


	public boolean empty() {
		return mTail.equals(this);
	}

	public E peek() {
		if (empty()) {
			throw new EmptyStackException();
		}
		return mHead;
	}

	public ImmutableStack<E> pop() {
		if (empty()) {
			throw new EmptyStackException();
		}
		return mTail;
	}

	public ImmutableStack<E> push(final E item) {
		return new ImmutableStack<>(item, this);
	}

	public int size() {
		int result = 0;
		for (ImmutableStack<E> stack = this; !stack.empty(); stack = stack.pop()) {
			++result;
		}
		return result;
	}
}
