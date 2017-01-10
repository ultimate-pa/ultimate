package de.uni_freiburg.informatik.ultimate.graphvr.server;

import java.util.HashMap;
import java.util.Map;

import com.google.protobuf.GeneratedMessageV3;

public class TypeRegistry {
	final protected Map<String, RegisteredType<?>> mByName = new HashMap<>();
	final protected Map<Class<?>, RegisteredType<?>> mByClass = new HashMap<>();

	final boolean registered(final String typeName) {
		return mByName.containsKey(typeName);
	}

	final <U extends GeneratedMessageV3> boolean registered(final Class<U> type) {
		return mByClass.containsKey(type);
	}

	final RegisteredType<? extends GeneratedMessageV3> get(final String typeName) {
		return mByName.get(typeName);
	}

	final RegisteredType<? extends GeneratedMessageV3> get(final Class<?> type) {
		return mByClass.get(type);
	}

	final <U extends GeneratedMessageV3> boolean register(final RegisteredType<U> type) {
		final boolean result = registered(type.type);
		mByClass.put(type.type, type);
		mByName.put(type.registeredName(), type);
		return result;
	}

	@Override
	public String toString() {
		return "[TypeRegistry] Registered Types: " + String.join(" ", mByName.keySet());
	}
}
