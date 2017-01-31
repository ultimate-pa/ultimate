package de.uni_freiburg.informatik.ultimate.servermodel.exceptions;

/**
 * This Exception is thrown, when a Client appears to have violated the Ultimate
 * Interactive Protocol.
 * 
 * @author Julian Jarecki
 *
 */
public class ClientCrazyException extends ClientException {
	private static final long serialVersionUID = 6163598721264845950L;
	// private WrappedProtoMessage mWrapped;

	public ClientCrazyException(/* WrappedProtoMessage wrapped */) {
		// this.mWrapped = wrapped;
	}

	/*
	 * public WrappedProtoMessage getWrapped() { return mWrapped; }
	 */
}
