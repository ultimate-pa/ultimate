package de.uni_freiburg.informatik.ultimate.interactive.utils;

import java.util.LinkedHashSet;
import java.util.Set;

public class InheritanceUtil {
	//private static Map<Class<?>, LinkedHashSet<Class<?>>> CACHE = new HashMap<>();

	public static <T> Set<Class<? extends T>> getInheritance(Class<? extends T> in, Class<T> bound) {
		LinkedHashSet<Class<? extends T>> result = new LinkedHashSet<Class<? extends T>>();

		result.add(in);
		getInheritance(in, result, bound);

		return result;
	}

	private static <T> void getInheritance(Class<? extends T> in, Set<Class<? extends T>> result, Class<T> bound) {
		final Class<?> superclass = getSuperclass(in);

		if (superclass != null && bound.isAssignableFrom(superclass)) {
			final Class<? extends T> castedSuperclass = (Class<? extends T>) superclass;
			if (result.add(castedSuperclass))
				getInheritance(castedSuperclass, result, bound);
		}

		getInterfaceInheritance(in, result, bound);
	}

	private static <T> void getInterfaceInheritance(Class<? extends T> in, Set<Class<? extends T>> result,
			Class<T> bound) {
		for (Class<?> I : in.getInterfaces()) {
			if (bound.isAssignableFrom(I)) {
				Class<? extends T> castedI = (Class<? extends T>) I;
				if (result.add(castedI))
					getInterfaceInheritance(castedI, result, bound);
			}
		}
	}

	private static Class<?> getSuperclass(Class<?> in) {
		if (in == null) {
			return null;
		}

		if (in.isArray() && in != Object[].class) {
			Class<?> type = in.getComponentType();

			while (type.isArray()) {
				type = type.getComponentType();
			}

			return type;
		}

		return in.getSuperclass();
	}
}
