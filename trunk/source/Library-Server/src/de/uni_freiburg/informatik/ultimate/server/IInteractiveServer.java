package de.uni_freiburg.informatik.ultimate.server;

import java.util.concurrent.ExecutionException;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.TimeoutException;

import de.uni_freiburg.informatik.ultimate.interactive.ITypeRegistry;

public interface IInteractiveServer<T> extends IServer {
	/**
	 * Blocks the calling Thread until a connection is established.
	 * 
	 * @throws InterruptedException
	 */
	Client<T> waitForConnection(final long timeout, final TimeUnit timeunit) throws InterruptedException, ExecutionException, TimeoutException;
	
	void setHelloMessage(final String helloMessage);

	ITypeRegistry<T> getTypeRegistry();
}
