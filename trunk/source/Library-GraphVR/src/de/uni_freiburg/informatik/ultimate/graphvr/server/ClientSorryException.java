package de.uni_freiburg.informatik.ultimate.graphvr.server;

public class ClientSorryException extends Exception {
	private static final long serialVersionUID = 4066976798408917275L;
	
	private WrappedProtoMessage mWrapped;

	public ClientSorryException(WrappedProtoMessage wrapped) {
		this.mWrapped = wrapped;
	}

	public WrappedProtoMessage getWrapped() {
		return mWrapped;
	}
}
