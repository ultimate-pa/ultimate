package de.uni_freiburg.informatik.ultimate.server;

import java.util.concurrent.CompletableFuture;

/**
 * Interface that provides a way for Ultimate Plugins to communicate with
 * Clients asynchronously in a type-safe manner.
 * 
 * @author Julian Jarecki
 *
 * @param <M>
 */
public interface IInteractive<M> extends IHandlerRegistry<M> {
	/**
	 * sends a data Object
	 * 
	 * @param data
	 */
	void send(M data);

	/**
	 * waits for a data Object
	 * 
	 * @param type
	 *            the type of the data Object must be supplied
	 * @return a Future containing the Clients answer.
	 */
	<T extends M> CompletableFuture<T> request(Class<T> type);

	/**
	 * waits for a data Object
	 * 
	 * @param type
	 *            the type of the data Object must be supplied (Thank you type
	 *            Erasure)
	 * @param data
	 *            the data Object itself
	 * @return a Future containing the Clients answer.
	 */
	<T extends M> CompletableFuture<T> request(Class<T> type, M data);

}
