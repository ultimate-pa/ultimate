package de.uni_freiburg.informatik.ultimate.interactive.exceptions;

import de.uni_freiburg.informatik.ultimate.interactive.IWrappedMessage;

/**
 * This Exception is thrown, when a Client is sending a SORRY-Message,
 * indicating, that it does not Provide the functionality that Ultimate
 * expected.
 * 
 * @author Julian Jarecki
 *
 */
public class ClientSorryException extends ClientException {
	private static final long serialVersionUID = 6163598721264845950L;
	private final IWrappedMessage<?> mWrapped;

	public ClientSorryException(final IWrappedMessage<?> wrapped) {
		mWrapped = wrapped;
	}

	@SuppressWarnings("unchecked")
	public <E> IWrappedMessage<E> getWrapped() {
		return (IWrappedMessage<E>) mWrapped;
	}
}
