package de.uni_freiburg.informatik.ultimate.server;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.function.Consumer;
import java.util.function.Function;
import java.util.function.Supplier;

import de.uni_freiburg.informatik.ultimate.interactive.IRegisteredType;
import de.uni_freiburg.informatik.ultimate.interactive.ITypeHandler;

public class TypeHandler<T> implements ITypeHandler<T> {
	private final IRegisteredType<T> mRegisteredType;
	private final List<Consumer<T>> mConsumers = new ArrayList<>();
	private final Map<Class<?>, Function<?, T>> mSuppliers = new HashMap<>();
	private Supplier<T> mSupplier;

	public TypeHandler(IRegisteredType<T> registeredType) {
		mRegisteredType = registeredType;
	}

	public void addConsumer(Consumer<T> consumer) {
		mConsumers.add(consumer);
	}

	public void setSupplier(Supplier<T> supplier) {
		mSupplier = supplier;
	}

	public <D> void setSupplier(Class<D> argType, Function<D, T> supplier) {
		mSuppliers.put(argType, supplier);
	}

	@Override
	public void consume(T data) {
		mConsumers.forEach(c -> c.accept(data));
	}

	@Override
	public T supply() {
		if (mSupplier == null)
			return mRegisteredType.getDefaultInstance();
		return mSupplier.get();
	}

	@SuppressWarnings("unchecked")
	final <D> Function<D, T> getSupplier(final Class<D> type) {
		return (Function<D, T>) mSuppliers.get(type);
	}

	@Override
	public <D> T supply(Class<D> argType, D data) {
		return getSupplier(argType).apply(data);
	}

}
