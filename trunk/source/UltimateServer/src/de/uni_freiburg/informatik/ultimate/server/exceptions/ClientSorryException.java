package de.uni_freiburg.informatik.ultimate.server.exceptions;

import de.uni_freiburg.informatik.ultimate.servercontroller.IWrappedMessage;

public class ClientSorryException extends Exception {
	private static final long serialVersionUID = 4066976798408917275L;

	private IWrappedMessage<?> mWrapped;

	public ClientSorryException(IWrappedMessage<?> wrapped) {
		this.mWrapped = wrapped;
	}

	public IWrappedMessage<?> getWrapped() {
		return mWrapped;
	}
}
