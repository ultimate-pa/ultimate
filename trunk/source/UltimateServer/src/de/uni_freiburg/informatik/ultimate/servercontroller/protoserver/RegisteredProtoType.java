package de.uni_freiburg.informatik.ultimate.servercontroller.protoserver;

import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;

import com.google.protobuf.GeneratedMessageV3;

import de.uni_freiburg.informatik.ultimate.interactive.IRegisteredType;

public class RegisteredProtoType<T extends GeneratedMessageV3> implements IRegisteredType<T> {
	private final Class<T> mType;
	private final T mDefaultMsg;

	protected RegisteredProtoType(final Class<T> type, final T defaultMsg) {
		this.mType = type;
		this.mDefaultMsg = defaultMsg;
	}

	@Override
	public String registeredName() {
		return registeredName(mDefaultMsg);
	}

	public static String registeredName(final GeneratedMessageV3 data) {
		return data.getDescriptorForType().getFullName();
	}

	public static <T extends GeneratedMessageV3> RegisteredProtoType<T> newInstance(final Class<T> type)
			throws NoSuchMethodException, SecurityException, IllegalAccessException, IllegalArgumentException,
			InvocationTargetException {

		final Method getDefaultInstance = type.getMethod("getDefaultInstance");
		final Object defaultInstance = getDefaultInstance.invoke(null);

		return new RegisteredProtoType<T>(type, (T) defaultInstance);
	}

	@Override
	public Class<T> getType() {
		return mType;
	}

	@Override
	public T getDefaultInstance() {
		return mDefaultMsg;
	}
}
