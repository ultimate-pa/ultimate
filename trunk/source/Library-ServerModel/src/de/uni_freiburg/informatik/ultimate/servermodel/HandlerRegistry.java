package de.uni_freiburg.informatik.ultimate.servermodel;

import java.util.HashMap;
import java.util.Map;
import java.util.function.Consumer;
import java.util.function.Function;
import java.util.function.Supplier;

public class HandlerRegistry<M> implements IHandlerRegistry<M> {
	private final ITypeRegistry<M> mTypeRegistry;
	final protected Map<String, TypeHandler<?>> mByName = new HashMap<>();
	final protected Map<Class<?>, TypeHandler<?>> mByClass = new HashMap<>();

	public HandlerRegistry(ITypeRegistry<M> typeRegistry) {
		mTypeRegistry = typeRegistry;
	}

	private final <T extends M> TypeHandler<T> register(IRegisteredType<T> type) {
		TypeHandler<T> typeHandler = new TypeHandler<>(type);
		mByClass.put(type.getClass(), typeHandler);
		mByName.put(type.registeredName(), typeHandler);

		return typeHandler;
	}

	@SuppressWarnings("unchecked")
	public final <T extends M> ITypeHandler<T> get(final String typeName) {
		if (mByName.containsKey(typeName)) {
			return (ITypeHandler<T>) mByName.get(typeName);
		}
		return register(mTypeRegistry.get(typeName));
	}

	public final <T extends M> ITypeHandler<T> get(final Class<T> type) {
		return get(type);
	}

	@SuppressWarnings("unchecked")
	private final <T extends M> TypeHandler<T> getInternal(final Class<T> type) {
		if (mByClass.containsKey(type)) {
			return (TypeHandler<T>) mByName.get(type);
		}
		return register(mTypeRegistry.get(type));
	}

	@Override
	public <T extends M> void register(Class<T> type, Consumer<T> consumer) {
		getInternal(type).addConsumer(consumer);
	}

	@Override
	public <T extends M> void register(Class<T> type, Supplier<T> supplier) {
		getInternal(type).setSupplier(supplier);
	}

	@Override
	public <D extends M, T extends M> void register(Class<T> type, Class<D> dataType, Function<D, T> supplier) {
		getInternal(type).setSupplier(dataType, supplier);
	}

}
