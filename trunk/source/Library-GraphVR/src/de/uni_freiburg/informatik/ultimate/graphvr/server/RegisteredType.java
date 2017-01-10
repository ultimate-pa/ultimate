package de.uni_freiburg.informatik.ultimate.graphvr.server;

import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.util.function.Consumer;

import com.google.protobuf.GeneratedMessageV3;

public class RegisteredType<T extends GeneratedMessageV3> {
	public final Consumer<T> consumer;
	public final Class<T> type;
	public final T defaultMsg;

	protected RegisteredType(final Class<T> type, final Consumer<T> consumer, final T defaultMsg) {
		this.consumer = consumer;
		this.type = type;
		this.defaultMsg = defaultMsg;
	}
	
	public String registeredName() {
		return registeredName(defaultMsg);
	}

	public static String registeredName(GeneratedMessageV3 data) {
		return data.getDescriptorForType().getFullName();
	}

	public static <T extends GeneratedMessageV3> RegisteredType<T> newInstance(final Class<T> type,
			final Consumer<T> consumer) throws NoSuchMethodException, SecurityException, IllegalAccessException,
			IllegalArgumentException, InvocationTargetException {

		final Method getDefaultInstance = type.getMethod("getDefaultInstance");
		final Object defaultInstance = getDefaultInstance.invoke(null);

		return new RegisteredType<T>(type, consumer, (T) defaultInstance);
	}
}
