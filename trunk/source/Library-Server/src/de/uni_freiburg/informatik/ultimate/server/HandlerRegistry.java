package de.uni_freiburg.informatik.ultimate.server;

import java.util.HashMap;
import java.util.Map;
import java.util.function.Consumer;
import java.util.function.Function;
import java.util.function.Supplier;

import de.uni_freiburg.informatik.ultimate.interactive.IHandlerRegistry;
import de.uni_freiburg.informatik.ultimate.interactive.IRegisteredType;
import de.uni_freiburg.informatik.ultimate.interactive.ITypeHandler;
import de.uni_freiburg.informatik.ultimate.interactive.ITypeRegistry;

public class HandlerRegistry<M> implements IHandlerRegistry<M> {
	private final ITypeRegistry<M> mTypeRegistry;
	final protected Map<String, TypeHandler<?>> mByName = new HashMap<>();
	final protected Map<Class<?>, TypeHandler<?>> mByClass = new HashMap<>();

	public HandlerRegistry(final ITypeRegistry<M> typeRegistry) {
		mTypeRegistry = typeRegistry;
	}

	private <T extends M> TypeHandler<T> register(final IRegisteredType<T> type) {
		final TypeHandler<T> typeHandler = new TypeHandler<>(type);
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
	private <T extends M> TypeHandler<T> getInternal(final Class<T> type) {
		if (mByClass.containsKey(type)) {
			return (TypeHandler<T>) mByName.get(type);
		}
		return register(mTypeRegistry.get(type));
	}

	@Override
	public <T extends M> void register(final Class<T> type, final Consumer<T> consumer) {
		getInternal(type).addConsumer(consumer);
	}

	@Override
	public <T extends M> void register(final Class<T> type, final Supplier<T> supplier) {
		getInternal(type).setSupplier(supplier);
	}

	@Override
	public <T extends M, D extends M> void register(final Class<T> type, final Class<D> dataType, final Function<D, T> supplier) {
		getInternal(type).setSupplier(dataType, supplier);
	}

}
