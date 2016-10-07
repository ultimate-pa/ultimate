package de.uni_freiburg.informatik.ultimate.deltadebugger.core.search.minimizers.algorithms;

import java.util.EmptyStackException;

/**
 * Immutable stack (effectively a singly linked list)
 *
 * @param <E> element type
 */
public class ImmutableStack<E> {
	private final E head;
	private final ImmutableStack<E> tail;

	@SuppressWarnings("rawtypes")
	public static final ImmutableStack EMPTY_STACK = new ImmutableStack();

	private ImmutableStack() {
		this.head = null;
		this.tail = this;
	}

	private ImmutableStack(E head, ImmutableStack<E> tail) {
		this.head = head;
		this.tail = tail;
	}
	
	@SuppressWarnings("unchecked")
	public static final <T> ImmutableStack<T> emptyStack() {
		return EMPTY_STACK;
	}

	public boolean empty() {
		return tail == this;
	}

	public ImmutableStack<E> push(E item) {
		return new ImmutableStack<>(item, this);
	}

	public ImmutableStack<E> pop() {
		if (empty()) {
			throw new EmptyStackException();
		}
		return tail;
	}

	public E peek() {
		if (empty()) {
			throw new EmptyStackException();
		}
		return head;
	}

	public int size() {
		int result = 0;
		for (ImmutableStack<E> stack = this; !stack.empty(); stack = stack.pop()) {
			++result;
		}
		return result;
	}

	@SafeVarargs
	public static <E> ImmutableStack<E> of(E... fifoItems) {
		ImmutableStack<E> stack = emptyStack();
		for (int i = fifoItems.length - 1; i >= 0; --i) {
			stack = stack.push(fifoItems[i]);
		}
		return stack;
	}
}