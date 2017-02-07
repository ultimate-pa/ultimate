package de.uni_freiburg.informatik.ultimate.server;

import java.util.concurrent.ExecutionException;
import java.util.concurrent.TimeoutException;

public interface IInteractiveServer<T> extends IServer {
	/**
	 * Blocks the calling Thread until a connection is established.
	 * 
	 * @throws InterruptedException
	 */
	Client<T> waitForConnection() throws InterruptedException, ExecutionException, TimeoutException;
}
