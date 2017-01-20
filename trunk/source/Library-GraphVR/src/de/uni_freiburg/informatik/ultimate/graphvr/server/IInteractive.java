package de.uni_freiburg.informatik.ultimate.graphvr.server;

import java.util.concurrent.CompletableFuture;
import java.util.function.Consumer;
import java.util.function.Supplier;

/**
 * 
 * 
 * @author iari
 *
 * @param <M>
 */
public interface IInteractive<M extends IMessage> {
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
	 *            the type of the data Object must be supplied (Thank you type
	 *            Erasure)
	 * @param data
	 *            the data Object itself
	 * @return a Future containing the Clients answer.
	 */
	<T extends M> CompletableFuture<T> request(Class<T> type, M data);

	/**
	 * registers a Data type with the Server.
	 * 
	 * Data types must be registered with {@link #register(Class)} or
	 * {@link #register(Class, Consumer)} before they can be sent or requested.
	 * 
	 * @param type
	 */
	<T extends M> void register(Class<T> type);

	/**
	 * registers a Data type with the Server with a Handler for incoming Data
	 * Objects of the type.
	 * 
	 * Data types must be registered with {@link #register(Class)} or
	 * {@link #register(Class, Consumer)} before they can be sent or requested.
	 * 
	 * @param type
	 * @param consumer
	 *            a consumer that will handle incoming data sent by the Client
	 *            on it's own account - i.e. not in response to a request.
	 */
	<T extends M> void register(Class<T> type, Consumer<T> consumer);

	/**
	 * registers a Data type with the Server with a Handler for incoming Data
	 * Objects of the type.
	 * 
	 * Data types must be registered with {@link #register(Class)} or
	 * {@link #register(Class, Consumer)} before they can be sent or requested.
	 * 
	 * @param type
	 * @param consumer
	 *            a consumer that will handle incoming data sent by the Client
	 *            on it's own account - i.e. not in response to a request.
	 */
	<T extends M> void register(Class<T> type, Supplier<T> supplier);
}
