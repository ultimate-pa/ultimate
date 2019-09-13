/*
 * Copyright (C) 2018 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2018 University of Freiburg
 *
 * This file is part of the ULTIMATE Core.
 *
 * The ULTIMATE Core is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Core is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Core. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Core, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Core grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.util;

import java.io.File;
import java.io.IOException;
import java.lang.reflect.Constructor;
import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.lang.reflect.Modifier;
import java.lang.reflect.Parameter;
import java.net.URISyntaxException;
import java.net.URL;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.Enumeration;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.function.Supplier;
import java.util.stream.Collectors;

/**
 * Utility class for reflection-based loading of operations, etc.
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class ReflectionUtil {

	private final static ExposedSecurityManager EXPOSED_SECURITY_MANAGER = new ExposedSecurityManager();
	private final static UrlConverter BUNDLE_RESOURCE_CONVERTER = createBundleResourceConverter();

	private ReflectionUtil() {
		// do not instantiate utility class
	}

	/**
	 * Create a UrlConverter taken from the core to handle bundle resources.
	 *
	 * If the core is not present, we do not need it as no OSGi loading can take place.
	 */
	private static UrlConverter createBundleResourceConverter() {
		final String qualifiedName = "de.uni_freiburg.informatik.ultimate.core.util.RcpUtils";
		try {
			final List<ClassLoader> loaders = getClassLoaders(ReflectionUtil.class);
			for (final ClassLoader loader : loaders) {
				final Class<?> clazz = getClassFromQualifiedName(qualifiedName, loader);
				if (clazz == null) {
					continue;
				}
				final Method method = clazz.getMethod("getBundleProtocolResolver");
				return (UrlConverter) method.invoke(null);
			}
			throw new ReflectionUtilException("Could not extract Class<?> from qualified name " + qualifiedName);
		} catch (NoSuchMethodException | SecurityException | IllegalAccessException | IllegalArgumentException
				| InvocationTargetException | ReflectionUtilException e) {
			return null;
		}
	}

	/**
	 * A (hopefully rather fast) method to obtain the class of a method caller.
	 *
	 * @param callStackDepth
	 *            The position in the current call stack for which you want to see the class. You are probably
	 *            interested in depth 3.
	 * @return The {@link Class} of the caller at the specified position.
	 */
	public static Class<?> getCallerClassName(final int callStackDepth) {
		return EXPOSED_SECURITY_MANAGER.getCallerClass(callStackDepth);
	}

	/**
	 * Return the name of the calling method up to the specified stack depth.
	 */
	public static String getCallerMethodName(final int callStackDepth) {
		final StackTraceElement[] callStack = Thread.currentThread().getStackTrace();
		if (callStack.length < callStackDepth) {
			return callStack[callStack.length - 1].getMethodName();
		}
		return callStack[callStackDepth].getMethodName();
	}

	/**
	 * Return a String specifying the calling method and its signature up to the given stack depth.
	 */
	public static String getCallerSignature(final int callStackDepth) {
		final StackTraceElement[] callStack = Thread.currentThread().getStackTrace();
		final StackTraceElement theFrame;
		if (callStack.length < callStackDepth) {
			theFrame = callStack[callStack.length - 1];
		} else {
			theFrame = callStack[callStackDepth];
		}
		return String.format("[L%4s] %15.15s.%s", theFrame.getLineNumber(),
				getCallerClassName(callStackDepth + 1).getSimpleName(), theFrame.getMethodName());
	}

	/**
	 * Finds all non-abstract classes implementing the given interface placed in the folder beside or below it.
	 */
	public static <T> Set<Class<? extends T>> getClassesImplementingInterfaceFromFolder(final Class<T> interfaceClazz) {
		if (interfaceClazz == null || !interfaceClazz.isInterface()) {
			throw new IllegalArgumentException(interfaceClazz + " does not represent a Java interface");
		}

		return getClassesFromFolder(interfaceClazz).stream().filter(a -> !isAbstractClass(a))
				.filter(a -> isClassImplementingInterface(a, interfaceClazz)).collect(Collectors.toSet());
	}

	/**
	 * Finds all classes in the folder beside or below the supplied anchor class.
	 */
	public static <T> Set<Class<? extends T>> getClassesFromFolder(final Class<T> anchorClazz) {
		if (anchorClazz == null) {
			return Collections.emptySet();
		}

		final Set<Class<? extends T>> result = new HashSet<>();
		final String packageName = anchorClazz.getPackage().getName();
		final Collection<File> files = getFolderContentsFromClass(anchorClazz);
		if (files == null) {
			return Collections.emptySet();
		}

		final List<ClassLoader> loaders = getClassLoaders(anchorClazz);
		for (final File file : files) {
			if (!file.getName().endsWith(".class")) {
				continue;
			}
			@SuppressWarnings("unchecked")
			final Class<? extends T> clazz = (Class<? extends T>) getClassFromFile(packageName, file, loaders);
			if (clazz == null) {
				continue;
			}
			result.add(clazz);
		}
		return result;
	}

	public static <T> T instantiateClass(final Class<T> clazz, final Object... params) {
		final ConstructorAndRemainingParameters<T> constructors = getConstructorsForClass(clazz, params);
		return constructors.instantiate();
	}

	public static <T> Supplier<T> getInstanceSupplier(final Class<T> clazz, final Object... params) {
		final ConstructorAndRemainingParameters<T> constructors = getConstructorsForClass(clazz, params);
		return () -> constructors.instantiate();
	}

	private static <T> ConstructorAndRemainingParameters<T> getConstructorsForClass(final Class<T> clazz,
			final Object... params) {
		if (clazz == null) {
			throw new IllegalArgumentException("clazz is null");
		}
		try {
			@SuppressWarnings("unchecked")
			final Constructor<T>[] constructors = (Constructor<T>[]) clazz.getDeclaredConstructors();
			if (constructors.length == 0) {
				throw new ReflectionUtilException(
						"Cannot instantiate class " + clazz.toString() + " because it has no constructors");
			}

			final Object[] newParams;
			if (clazz.isMemberClass() && !Modifier.isStatic(clazz.getModifiers())) {
				// this class is a non-static inner class of another one
				final Class<?> enclosingClazz = clazz.getEnclosingClass();
				final ConstructorAndRemainingParameters<?> enclosingClazzConstructor =
						getConstructorsForClass(enclosingClazz, params);

				final Object enclosingClazzInstance = enclosingClazzConstructor.instantiate();
				final Object[] remainingParams = enclosingClazzConstructor.mUnusedParameters;

				if (remainingParams == null || remainingParams.length == 0) {
					newParams = new Object[] { enclosingClazzInstance };
				} else {
					newParams = new Object[remainingParams.length + 1];
					newParams[0] = enclosingClazzInstance;
					System.arraycopy(remainingParams, 0, newParams, 1, remainingParams.length);
				}
			} else {
				newParams = params;
			}

			// filter all constructors which are valid and require less or equal the amount of parameters we have
			final List<Constructor<T>> constructorCandidates = Arrays.stream(constructors)
					.filter(a -> a.getParameterCount() <= newParams.length).collect(Collectors.toList());

			if (constructorCandidates.isEmpty()) {
				throw new ReflectionUtilException("Cannot instantiate class " + clazz.toString()
						+ " because there is no constructor that takes " + newParams.length + " arguments");
			}

			// we will try and select the constructor which matches the most parameters that we have
			int maxMatch = -1;
			Constructor<T> candidateConstructor = null;
			for (final Constructor<T> current : constructorCandidates) {
				final Parameter[] parameters = current.getParameters();
				int matched = 0;
				for (final Parameter parameter : parameters) {
					final Class<?> availableType = parameter.getType();
					if (newParams[matched] == null && !availableType.isPrimitive()) {
						// this should match
					} else {
						final Class<?> wrappedAvailableType = toWrapperClazz(availableType);
						final Class<?> suppliedType = newParams[matched].getClass();
						if (!wrappedAvailableType.isAssignableFrom(suppliedType)) {
							matched = -1;
							break;
						}
					}
					matched++;
				}
				if (matched > maxMatch) {
					maxMatch = matched;
					candidateConstructor = current;
				}
			}

			if (candidateConstructor == null) {
				throw new ReflectionUtilException(
						"Cannot instantiate class " + clazz.toString() + " because I did not find a valid constructor");
			}
			final Object[] usedParams = new Object[maxMatch];
			final Object[] remainingParams = new Object[newParams.length - maxMatch];
			System.arraycopy(newParams, 0, usedParams, 0, maxMatch);
			System.arraycopy(newParams, maxMatch, remainingParams, 0, newParams.length - maxMatch);
			return new ConstructorAndRemainingParameters<>(candidateConstructor, clazz, usedParams, remainingParams);
		} catch (final SecurityException e) {
			throw new ReflectionUtilException(
					"Cannot instantiate class " + clazz.toString() + " because I am not allowed to access it", e);
		} catch (final IllegalArgumentException e) {
			throw new AssertionError(
					"Cannot instantiate class " + clazz.toString() + " because the parameters do not match", e);
		}
	}

	/**
	 * Return the filenames of the files in the given directory. We use the classloader to get the URL of this folder.
	 * We support only URLs with protocol <i>file</i>.
	 */
	private static Collection<File> getFilesFromDirectoryResources(final ClassLoader loader,
			final List<String> resourceNames) {
		final Set<File> rtr = new HashSet<>();
		for (final String resourceName : resourceNames) {
			rtr.addAll(getFilesFromDirectoryResource(loader, resourceName));
		}
		return rtr;
	}

	/**
	 * Return the filenames of the files in the given directory. We use the classloader to get the URL of this folder.
	 * We support only URLs with protocol <i>file</i>.
	 */
	private static Collection<File> getFilesFromDirectoryResource(final ClassLoader loader, final String resourceName) {
		final URL dirUrl = loader.getResource(resourceName);
		if (dirUrl == null) {
			throw new ReflectionUtilException("Could not resolve resource " + resourceName);
		}
		return getFilesFromDirectoryResource(loader, dirUrl);
	}

	/**
	 * Return the filenames of the files specified by the given resource URL. We use the classloader to get the URL of
	 * this folder. We support only URLs with protocol <i>file</i> or <i>bundleresource</i>.
	 */
	private static Collection<File> getFilesFromDirectoryResource(final ClassLoader loader, final URL url) {
		final String protocol = url.getProtocol();
		final File dirFile;
		if ("file".equals(protocol)) {
			try {
				dirFile = new File(url.toURI());
			} catch (final URISyntaxException e) {
				return Collections.emptySet();
			}
		} else if ("bundleresource".equals(protocol)) {
			if (BUNDLE_RESOURCE_CONVERTER == null) {
				throw new AssertionError("Someone supplied a bundleresource resource but we do not have a converter -- "
						+ "check if this deployable is built correctly "
						+ "(maybe de.uni_freiburg.informatik.ultimate.core is missing?)");
			}
			try {
				final URL fileUrl = BUNDLE_RESOURCE_CONVERTER.convert(url);
				dirFile = new File(fileUrl.getFile());
			} catch (final IOException e) {
				return Collections.emptySet();
			}
		} else {
			throw new UnsupportedOperationException("unknown protocol " + protocol);
		}
		return CoreUtil.flattenDirectories(Collections.singleton(dirFile));
	}

	/**
	 * @return true if clazz represents an abstract class, false otherwise
	 */
	public static boolean isAbstractClass(final Class<?> clazz) {
		return Modifier.isAbstract(clazz.getModifiers());
	}

	private static Class<?> getClassFromFile(final String packageName, final File file) {
		return getClassFromFile(packageName, file, Collections.emptyList());
	}

	private static Class<?> getClassFromFile(final String packageName, final File file,
			final Collection<ClassLoader> loaders) {
		final String qualifiedName = getQualifiedNameFromFile(packageName, file);
		if (loaders.isEmpty()) {
			return getClassFromQualifiedName(qualifiedName);
		}
		for (final ClassLoader loader : loaders) {
			final Class<?> clazz = getClassFromQualifiedName(qualifiedName, loader);
			if (clazz != null) {
				return clazz;
			}
		}
		throw new ReflectionUtilException("Could not extract Class<?> from qualified name " + qualifiedName);
	}

	/**
	 * Create a {@link Class} instance from a fully qualified name
	 */
	private static Class<?> getClassFromQualifiedName(final String qualifiedName) {
		try {
			return Class.forName(qualifiedName);
		} catch (final ClassNotFoundException e) {
			throw new ReflectionUtilException("Could not extract Class<?> from qualified name " + qualifiedName, e);
		}
	}

	/**
	 * Create a {@link Class} instance from a fully qualified name and a given classloader. Do not throw an exception,
	 * but let the caller do that.
	 *
	 * @param loader
	 */
	private static Class<?> getClassFromQualifiedName(final String qualifiedName, final ClassLoader loader) {
		try {
			return Class.forName(qualifiedName, true, loader);
		} catch (final ClassNotFoundException e) {
			return null;
		}
	}

	/**
	 * Tries to resolve the fully qualified name from the package name and the found file. If the package is a.b.c.d and
	 * we found a class with the path /foo/bar/a/b/c/d/huh/OurClass.class, then the fully qualified name is
	 * a.b.c.d.huh.OurClass
	 */
	private static String getQualifiedNameFromFile(final String packageName, final File file) {
		assert file != null;
		assert file.getName().endsWith(".class");

		final String fullname = file.getAbsolutePath();
		final String filenameWithoutSuffix = fullname.substring(0, fullname.length() - 6);
		final String knownPath = getPathFromPackageName(packageName);
		final int validAfter = filenameWithoutSuffix.indexOf(knownPath);
		assert validAfter != -1;

		return filenameWithoutSuffix.substring(validAfter).replace(File.separatorChar, '.');
	}

	private static String getPathFromPackageName(final String packageName) {
		return packageName.replace(".", File.separator);
	}

	private static ClassLoader getClassLoader(final Class<?> clazz) {
		ClassLoader loader = clazz.getClassLoader();
		if (loader == null) {
			// Try the bootstrap classloader - obtained from the ultimate parent of the System Class Loader.
			loader = ClassLoader.getSystemClassLoader();
			while (loader != null && loader.getParent() != null) {
				loader = loader.getParent();
			}
		}
		return loader;
	}

	private static List<ClassLoader> getClassLoaders(final Class<?> clazz) {
		final List<ClassLoader> rtr = new ArrayList<>();
		ClassLoader loader = clazz.getClassLoader();
		if (loader == null) {
			// Try the bootstrap classloader - obtained from the ultimate parent of the System Class Loader.
			loader = ClassLoader.getSystemClassLoader();
		}
		while (loader != null) {
			rtr.add(loader);
			loader = loader.getParent();
		}
		return rtr;
	}

	/**
	 * Return the contents of the folder from which this class was loaded.
	 */
	private static Collection<File> getFolderContentsFromClass(final Class<?> clazz) {
		if (clazz == null) {
			return null;
		}
		final ClassLoader loader = getClassLoader(clazz);
		if (loader == null) {
			return Collections.emptyList();
		}

		final String packageName = clazz.getPackage().getName();
		final String packagePath = getPathFromPackageName(packageName);

		final Enumeration<URL> resourceUrlsIter;
		try {
			resourceUrlsIter = loader.getResources(packagePath);
		} catch (final IOException e) {
			throw new ReflectionUtilException(
					"Classloader " + loader.toString() + " could not load resource " + packagePath, e);
		}

		final List<File> rtr = new ArrayList<>();
		while (resourceUrlsIter.hasMoreElements()) {
			final URL resourceUrl = resourceUrlsIter.nextElement();
			rtr.addAll(getFilesFromDirectoryResource(loader, resourceUrl));
		}
		return rtr;
	}

	/**
	 * Checks if the given class implements a given interface.
	 * <p>
	 * The check also checks whether a superclass implements the interface.
	 *
	 * @param clazzIn
	 *            the class object to check
	 * @return true if and only if <code>clazzIn</code> implements <code>interfaceClazz</code>. Otherwise false.
	 */
	public static boolean isClassImplementingInterface(final Class<?> clazzIn, final Class<?> interfaceClazz) {
		if (interfaceClazz == null || !interfaceClazz.isInterface()) {
			throw new IllegalArgumentException("interfaceClazz does not represent an interface");
		}

		Class<?> clazz = clazzIn;
		while (clazz != null) {
			final Class<?>[] implementedInterfaces = clazz.getInterfaces();
			for (final Class<?> interFace : implementedInterfaces) {
				if (interFace.equals(interfaceClazz)) {
					// class implements IOperation in a transitive chain
					return true;
				}
			}
			clazz = clazz.getSuperclass();
		}
		return false;
	}

	public static boolean isSubclassOfClass(final Class<?> clazzIn, final Class<?> superClazz) {
		if (superClazz == null) {
			throw new IllegalArgumentException("superClazz is null");
		}
		if (Modifier.isFinal(superClazz.getModifiers())) {
			return false;
		}
		if (clazzIn == null) {
			return true;
		}
		return superClazz.isAssignableFrom(clazzIn);
	}

	private static Class<?> toWrapperClazz(final Class<?> clazz) {
		if (!clazz.isPrimitive()) {
			return clazz;
		}

		if (clazz == Integer.TYPE) {
			return Integer.class;
		}
		if (clazz == Long.TYPE) {
			return Long.class;
		}
		if (clazz == Boolean.TYPE) {
			return Boolean.class;
		}
		if (clazz == Byte.TYPE) {
			return Byte.class;
		}
		if (clazz == Character.TYPE) {
			return Character.class;
		}
		if (clazz == Float.TYPE) {
			return Float.class;
		}
		if (clazz == Double.TYPE) {
			return Double.class;
		}
		if (clazz == Short.TYPE) {
			return Short.class;
		}
		if (clazz == Void.TYPE) {
			return Void.class;
		}
		throw new UnsupportedOperationException("Not yet implemented: wrapper for " + clazz);
	}

	private static final class ConstructorAndRemainingParameters<T> {
		private final Constructor<T> mConstructor;
		private final Class<T> mClazz;
		private final Object[] mMatchedParameters;
		private final Object[] mUnusedParameters;

		private ConstructorAndRemainingParameters(final Constructor<T> constructor, final Class<T> clazz,
				final Object[] matchedParameters, final Object[] remainingParameters) {
			mConstructor = constructor;
			mClazz = clazz;
			mMatchedParameters = matchedParameters;
			mUnusedParameters = remainingParameters;
		}

		public T instantiate() {
			assert mConstructor.getParameterCount() == mMatchedParameters.length : "Wrong length";
			try {
				return mConstructor.newInstance(mMatchedParameters);
			} catch (final SecurityException | InstantiationException | IllegalAccessException e) {
				throw new ReflectionUtilException(
						"Cannot instantiate class " + mClazz.toString() + " because I am not allowed to access it", e);
			} catch (final IllegalArgumentException e) {
				throw new AssertionError(
						"Cannot instantiate class " + mClazz.toString() + " because the parameters do not match", e);
			} catch (final InvocationTargetException e) {
				throw new ReflectionUtilException(
						"Cannot instantiate class " + mClazz.toString() + " because the constructor threw an exception",
						e);
			}
		}
	}

	/**
	 * A custom security manager that exposes the getClassContext() information
	 */
	private static final class ExposedSecurityManager extends SecurityManager {
		public Class<?> getCallerClass(final int callStackDepth) {
			return getClassContext()[callStackDepth];
		}
	}

	/**
	 * A {@link RuntimeException} that will be thrown for unsuccessful operations of {@link ReflectionUtil}.
	 *
	 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
	 *
	 */
	private static final class ReflectionUtilException extends RuntimeException {

		private static final long serialVersionUID = -5821955867584671607L;

		public ReflectionUtilException(final String message) {
			super(message);
		}

		public ReflectionUtilException(final String message, final Throwable cause) {
			super(message, cause);
		}
	}

	/**
	 * Interface that allows me to indirectly instantiate a converter without adding the dependency explicitly.
	 *
	 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
	 *
	 */
	@FunctionalInterface
	public interface UrlConverter {
		public URL convert(URL url) throws IOException;
	}

}
