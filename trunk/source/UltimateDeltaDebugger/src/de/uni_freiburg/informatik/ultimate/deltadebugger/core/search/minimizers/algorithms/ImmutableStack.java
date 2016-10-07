package de.uni_freiburg.informatik.ultimate.deltadebugger.core.search.minimizers.algorithms;

import java.util.EmptyStackException;

/**
 * Immutable stack (effectively a singly linked list)
 *
 * @param <E>
 *            element type
 */
public class ImmutableStack<E> {
	@SuppressWarnings("rawtypes")
	public static final ImmutableStack EMPTY_STACK = new ImmutableStack();

	@SuppressWarnings("unchecked")
	public static final <T> ImmutableStack<T> emptyStack() {
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

	private final E head;

	private final ImmutableStack<E> tail;

	private ImmutableStack() {
		this.head = null;
		this.tail = this;
	}

	private ImmutableStack(final E head, final ImmutableStack<E> tail) {
		this.head = head;
		this.tail = tail;
	}

	public boolean empty() {
		return tail == this;
	}

	public E peek() {
		if (empty()) {
			throw new EmptyStackException();
		}
		return head;
	}

	public ImmutableStack<E> pop() {
		if (empty()) {
			throw new EmptyStackException();
		}
		return tail;
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