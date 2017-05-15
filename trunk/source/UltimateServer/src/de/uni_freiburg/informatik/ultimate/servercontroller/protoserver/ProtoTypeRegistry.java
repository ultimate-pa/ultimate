package de.uni_freiburg.informatik.ultimate.servercontroller.protoserver;

import java.lang.reflect.InvocationTargetException;
import java.util.HashMap;
import java.util.Map;

import com.google.protobuf.GeneratedMessageV3;

import de.uni_freiburg.informatik.ultimate.interactive.IRegisteredType;
import de.uni_freiburg.informatik.ultimate.interactive.ITypeRegistry;

public class ProtoTypeRegistry implements ITypeRegistry<GeneratedMessageV3> {
	final protected Map<String, RegisteredProtoType<?>> mByName = new HashMap<>();
	final protected Map<Class<?>, RegisteredProtoType<?>> mByClass = new HashMap<>();

	@Override
	public final boolean registered(final String typeName) {
		return mByName.containsKey(typeName);
	}

	@Override
	public final <U extends GeneratedMessageV3> boolean registered(final Class<U> type) {
		return mByClass.containsKey(type);
	}

	@Override
	@SuppressWarnings("unchecked")
	public final <T extends GeneratedMessageV3> IRegisteredType<T> get(final String typeName) {
		return (RegisteredProtoType<T>) mByName.get(typeName);
	}

	@Override
	@SuppressWarnings("unchecked")
	public final <T extends GeneratedMessageV3> RegisteredProtoType<T> get(final Class<T> type) {
		return (RegisteredProtoType<T>) mByClass.get(type);
	}

	private <U extends GeneratedMessageV3> boolean register(final RegisteredProtoType<U> type) {
		final boolean result = registered(type.getType());
		mByClass.put(type.getType(), type);
		mByName.put(type.registeredName(), type);
		return result;
	}

	@Override
	public String toString() {
		return "[TypeRegistry] Registered Types: " + String.join(" ", mByName.keySet());
	}

	@Override
	public <T extends GeneratedMessageV3> void register(final Class<T> type) {
		try {
			final RegisteredProtoType<T> regType = RegisteredProtoType.newInstance(type);
			register(regType);
		} catch (NoSuchMethodException | SecurityException | IllegalAccessException | IllegalArgumentException
				| InvocationTargetException e) {
			throw new IllegalStateException(e);
		}
	}
}
