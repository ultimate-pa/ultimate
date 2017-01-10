package de.uni_freiburg.informatik.ultimate.graphvr.server;

import java.util.concurrent.CompletableFuture;
import java.util.function.Consumer;

import com.google.protobuf.GeneratedMessageV3;

public interface IProtoServer {
	/**
	 * Starts the Server listening to a single connection.
	 */
	void start();

	/**
	 * shuts down the Server.
	 */
	void stop();

	/**
	 * initial message to the client. must be called before other transactions
	 * 
	 * @param data
	 *            optional data object
	 */
	void hello(GeneratedMessageV3 data);

	/**
	 * sends a data Object
	 * 
	 * @param data
	 */
	void send(GeneratedMessageV3 data);

	/**
	 * waits for a data Object
	 * 
	 * @param type
	 *            the type of the data Object must be supplied (Thank you type
	 *            Erasure)
	 * @param data
	 *            the data Object itsself
	 * @return a Future containing the Clients answer.
	 */
	<T extends GeneratedMessageV3> CompletableFuture<T> request(Class<T> type, GeneratedMessageV3 data);

	/**
	 * sends a string message that is supposed to be shown on the Client
	 * 
	 * @param msg
	 */
	void send(String msg);

	/**
	 * registers a Data type with the Server.
	 * 
	 * Data types must be registered with {@link #register(Class)} or
	 * {@link #register(Class, Consumer)} before they can be sent or requested.
	 * 
	 * @param type
	 */
	<T extends GeneratedMessageV3> void register(Class<T> type);

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
	<T extends GeneratedMessageV3> void register(Class<T> type, Consumer<T> consumer);

	/**
	 * Blocks the calling Thread until a connection is established.
	 */
	void waitForConnection();
}
