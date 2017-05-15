package de.uni_freiburg.informatik.ultimate.interactive.utils;

import java.util.LinkedHashSet;
import java.util.Set;

public class InheritanceUtil {
	// private static Map<Class<?>, LinkedHashSet<Class<?>>> CACHE = new HashMap<>();

	public static <T> Set<Class<? extends T>> getInheritance(final Class<? extends T> ofChildType,
			final Class<T> bound) {
		final LinkedHashSet<Class<? extends T>> result = new LinkedHashSet<Class<? extends T>>();

		result.add(ofChildType);
		getInheritance(ofChildType, result, bound);

		return result;
	}

	private static <T> void getInheritance(final Class<? extends T> ofChildType, final Set<Class<? extends T>> result,
			final Class<T> bound) {
		final Class<?> superclass = getSuperclass(ofChildType);

		if (superclass != null && bound.isAssignableFrom(superclass)) {
			@SuppressWarnings("unchecked")
			final Class<? extends T> castedSuperclass = (Class<? extends T>) superclass;
			if (result.add(castedSuperclass))
				getInheritance(castedSuperclass, result, bound);
		}

		getInterfaceInheritance(ofChildType, result, bound);
	}

	private static <T> void getInterfaceInheritance(final Class<? extends T> ofChildType,
			final Set<Class<? extends T>> result, final Class<T> bound) {
		for (final Class<?> I : ofChildType.getInterfaces()) {
			if (bound.isAssignableFrom(I)) {
				@SuppressWarnings("unchecked")
				final Class<? extends T> castedI = (Class<? extends T>) I;
				if (result.add(castedI))
					getInterfaceInheritance(castedI, result, bound);
			}
		}
	}

	private static Class<?> getSuperclass(final Class<?> ofChildType) {
		if (ofChildType == null) {
			return null;
		}

		if (ofChildType.isArray() && ofChildType != Object[].class) {
			Class<?> type = ofChildType.getComponentType();

			while (type.isArray()) {
				type = type.getComponentType();
			}

			return type;
		}

		return ofChildType.getSuperclass();
	}
}
