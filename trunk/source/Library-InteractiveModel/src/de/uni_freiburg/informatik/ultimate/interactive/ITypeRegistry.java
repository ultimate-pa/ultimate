package de.uni_freiburg.informatik.ultimate.interactive;

/**
 * 
 * 
 * @author Julian Jarecki
 *
 * @param <M>
 */
public interface ITypeRegistry<M> {
	<T extends M> boolean registered(Class<T> type);

	<T extends M> boolean registered(String typeName);

	<T extends M> IRegisteredType<T> get(String typeName);

	<T extends M> IRegisteredType<T> get(Class<T> type);

	/**
	 * registers a Data type with the Server.
	 * 
	 * Data types must be registered with {@link #register(Class)} before they
	 * can be sent or requested.
	 * 
	 * @param type
	 */
	<T extends M> void register(Class<T> type);
}
