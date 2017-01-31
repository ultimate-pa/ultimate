package de.uni_freiburg.informatik.ultimate.servermodel.exceptions;

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
	// private WrappedProtoMessage mWrapped;

	public ClientSorryException(/* WrappedProtoMessage wrapped */) {
		// this.mWrapped = wrapped;
	}

	/*
	 * public WrappedProtoMessage getWrapped() { return mWrapped; }
	 */
}
