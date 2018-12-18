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
import java.net.URISyntaxException;
import java.net.URL;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.Enumeration;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

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
		try {
			final Class<?> clazz = getClassFromQualifiedName("de.uni_freiburg.informatik.ultimate.core.util.RcpUtils");
			final Method method = clazz.getMethod("getBundleProtocolResolver");
			return (UrlConverter) method.invoke(null);
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
	 * Finds all classes implementing the given interface placed in the folder beside or below it.
	 */
	public static Set<Class<?>> getClassesImplementingInterfaceFromFolder(final Class<?> interfaceClazz) {
		if (interfaceClazz == null) {
			return Collections.emptySet();
		}

		final Set<Class<?>> result = new HashSet<>();
		final String packageName = interfaceClazz.getPackage().getName();
		final Collection<File> files = getFolderContentsFromClass(interfaceClazz);
		if (files == null) {
			return Collections.emptySet();
		}

		for (final File file : files) {
			final Class<?> clazz = retrieveClassFromFile(packageName, file, interfaceClazz);
			if (clazz == null) {
				continue;
			}
			result.add(clazz);
		}
		return result;
	}

	public static <T> T instantiate(final Class<T> clazz) {
		if (clazz == null) {
			throw new IllegalArgumentException("clazz is null");
		}
		try {
			final Constructor<?>[] constructors = clazz.getDeclaredConstructors();
			if (constructors.length == 0) {
				throw new ReflectionUtilException(
						"Cannot instantiate class " + clazz.toString() + " because it has no constructors");
			}

			if (clazz.isMemberClass() && !Modifier.isStatic(clazz.getModifiers())) {
				// this class is a non-static inner class of another one
				final Class<?> enclosingClazz = clazz.getEnclosingClass();
				final Object enclosingClazzInstance = instantiate(enclosingClazz);
				return clazz.getConstructor(enclosingClazz).newInstance(enclosingClazzInstance);
			}

			return clazz.getConstructor().newInstance();
		} catch (final NoSuchMethodException e) {
			throw new ReflectionUtilException(
					"Cannot instantiate class " + clazz.toString() + " because I did not find a valid constructor", e);
		} catch (final SecurityException | InstantiationException | IllegalAccessException e) {
			throw new ReflectionUtilException(
					"Cannot instantiate class " + clazz.toString() + " because I am not allowed to access it", e);
		} catch (final IllegalArgumentException e) {
			throw new AssertionError(
					"Cannot instantiate class " + clazz.toString() + " because the parameters do not match", e);
		} catch (final InvocationTargetException e) {
			throw new ReflectionUtilException(
					"Cannot instantiate class " + clazz.toString() + " because the constructor threw an exception", e);
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
	 * this folder. We support only URLs with protocol <i>file</i>.
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
	public static boolean classIsAbstract(final Class<?> clazz) {
		return Modifier.isAbstract(clazz.getModifiers());
	}

	private static Class<?> retrieveClassFromFile(final String packageName, final File file,
			final Class<?> interfaceClazz) {
		if (!file.getName().endsWith(".class")) {
			return null;
		}
		final Class<?> clazz = getClassFromFile(packageName, file);
		if (clazz == null) {
			return null;
		}
		if (classIsAbstract(clazz)) {
			return null;
		}
		if (!classImplementsInterface(clazz, interfaceClazz)) {
			return null;
		}
		return clazz;
	}

	private static Class<?> getClassFromFile(final String packageName, final File file) {
		final String qualifiedName = getQualifiedNameFromFile(packageName, file);
		return getClassFromQualifiedName(qualifiedName);
	}

	/**
	 * Create a {@link Class} instance from a fully qualified name
	 */
	public static Class<?> getClassFromQualifiedName(final String qualifiedName) {
		try {
			return Class.forName(qualifiedName);
		} catch (final ClassNotFoundException e) {
			throw new ReflectionUtilException("Could not extract Class<?> from qualified name " + qualifiedName, e);
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

	/**
	 * Return the contents of the folder from which this class was loaded.
	 */
	public static Collection<File> getFolderContentsFromClass(final Class<?> clazz) {
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

			// if ("file".equals(resourceUrl.getProtocol())) {
			// InputStream in = null;
			// try {
			// in = resourceUrl.openStream();
			// if (in != null) {
			// final BufferedReader br = new BufferedReader(new InputStreamReader(in));
			// String resource = br.readLine();
			// while (resource != null) {
			// filenames.add(packagePath + File.separator + resource);
			// resource = br.readLine();
			// }
			// }
			// } catch (final IOException e) {
			// throw new ReflectionUtilException("Could not read from or open stream for resource " + resourceUrl
			// + " after already reading " + filenames.size() + " files", e);
			// } finally {
			// if (in != null) {
			// try {
			// in.close();
			// } catch (final IOException e) {
			// throw new ReflectionUtilException(
			// "Expcetion during closing of resource input stream " + resourceUrl, e);
			// }
			// }
			// }
			// } else {
			//
			// }
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
	public static boolean classImplementsInterface(final Class<?> clazzIn, final Class<?> interfaceClazz) {
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
