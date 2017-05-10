package de.uni_freiburg.informatik.ultimate.interactive;

import java.util.concurrent.CompletableFuture;

/**
 * Interface that provides a way for Ultimate Plugins to communicate with Clients asynchronously in a type-safe manner.
 * 
 * @author Julian Jarecki
 *
 * @param <M>
 */
public interface IInteractiveQueue<M> {
	/**
	 * sends a data Object
	 * 
	 * @param data
	 */
	void send(final M data);

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
	 *            the type of the data Object must be supplied (Thank you type Erasure)
	 * @param data
	 *            the data Object itself
	 * @return a Future containing the Clients answer.
	 */
	<T extends M> CompletableFuture<T> request(Class<T> type, M data);

	static <M> IInteractiveQueue<M> dummy() {
		return new IInteractiveQueue<M>() {
			private final static String ERROR_MSG = "Dummy Interface.";

			@Override
			public void send(final M data) {
				throw new IllegalAccessError(ERROR_MSG);
			}

			@Override
			public <T extends M> CompletableFuture<T> request(final Class<T> type) {
				final CompletableFuture<T> result = new CompletableFuture<>();
				result.completeExceptionally(new IllegalAccessError(ERROR_MSG));
				return result;
			}

			@Override
			public <T extends M> CompletableFuture<T> request(final Class<T> type, final M data) {
				return request(type);
			}
		};
	}

}
