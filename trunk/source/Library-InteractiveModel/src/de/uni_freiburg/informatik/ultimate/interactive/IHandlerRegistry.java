package de.uni_freiburg.informatik.ultimate.interactive;

import java.util.function.Consumer;
import java.util.function.Function;
import java.util.function.Supplier;

/**
 * Interface that allows to register consumers and suppliers that allow
 * asynchronous handling of incoming data types and requests.
 * 
 * @author Julian Jarecki
 *
 * @param <M>
 */
public interface IHandlerRegistry<M> {
	/**
	 * registers a Handler for incoming Data Objects of a registered type.
	 * 
	 * Data types must be registered with {@link ITypeRegistry#register(Class)}
	 * before handlers or suppliers can be registered.
	 * 
	 * @param type
	 * @param consumer
	 *            a consumer that will handle incoming data sent by the Client
	 *            on it's own account - i.e. not in response to a request.
	 */
	<T extends M> void register(Class<T> type, Consumer<T> consumer);

	/**
	 * registers a Supplier for incoming Data Requests of a given registered
	 * type.
	 * 
	 * Data types must be registered with {@link ITypeRegistry#register(Class)}
	 * before handlers or suppliers can be registered.
	 * 
	 * @param type
	 * @param supplier
	 *            a supplier that will generate the type if requested by the
	 *            Client.
	 */
	<T extends M> void register(Class<T> type, Supplier<T> supplier);

	/**
	 * registers a Supplier for incoming Data Requests of a given registered
	 * type.
	 * 
	 * Data types must be registered with {@link ITypeRegistry#register(Class)}
	 * before handlers or suppliers can be registered.
	 *
	 * @param dataType
	 *            type of a piece of data that is sent with the request
	 * @param type
	 * @param supplier
	 *            a supplier that will generate the type if requested by the
	 *            Client depending on data sent with the request.
	 */
	<T extends M, D extends M> void register(Class<T> type, Class<D> dataType, Function<D, T> supplier);
}
