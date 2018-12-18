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

import java.io.BufferedReader;
import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.lang.reflect.Modifier;
import java.net.URISyntaxException;
import java.net.URL;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.Deque;
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

	private ReflectionUtil() {
		// do not instantiate utility class
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
		final ClassLoader classLoader = interfaceClazz.getClassLoader();
		final String packageName = interfaceClazz.getPackage().getName();
		final List<String> filenames = getFolderContentsFromClass(interfaceClazz);
		if (filenames == null) {
			return Collections.emptySet();
		}

		final Collection<File> files = filesInDirectory(classLoader, filenames);
		for (final File file : files) {
			final Class<?> clazz = retrieveClassFromFile(packageName, file, interfaceClazz);
			if (clazz == null) {
				continue;
			}
			result.add(clazz);
		}
		return result;
	}

	/**
	 * Return the filenames of the files in the given directory. We use the classloader to get the URL of this folder.
	 * We support only URLs with protocol <i>file</i>.
	 */
	private static Collection<File> filesInDirectory(final ClassLoader loader, final List<String> resourceNames) {
		final Set<File> rtr = new HashSet<>();
		for (final String filename : resourceNames) {
			final URL dirUrl = loader.getResource(filename);
			if (dirUrl == null) {
				continue;
			}
			final String protocol = dirUrl.getProtocol();
			final File dirFile;
			if ("file".equals(protocol)) {
				try {
					dirFile = new File(dirUrl.toURI());
				} catch (final URISyntaxException e) {
					continue;
				}
			}
			// TODO: We need a dependency on eclipse for this protocol
			// else if ("bundleresource".equals(protocol)) {
			// try {
			// final URL fileUrl = FileLocator.toFileURL(dirUrl);
			// dirFile = new File(fileUrl.getFile());
			// } catch (final Exception e) {
			// return Collections.emptyList();
			// }
			// }
			else {
				throw new UnsupportedOperationException("unknown protocol " + protocol);
			}
			rtr.addAll(resolveDirectories(Arrays.asList(dirFile)));
		}
		return rtr;
	}

	private static Collection<File> resolveDirectories(final Collection<File> files) {
		final Deque<File> worklist = new ArrayDeque<>();
		final List<File> rtr = new ArrayList<>();
		worklist.addAll(files);
		while (!worklist.isEmpty()) {
			final File file = worklist.removeFirst();
			if (file.isFile()) {
				rtr.add(file);
				continue;
			}
			worklist.addAll(Arrays.asList(file.listFiles()));
		}
		return rtr;
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
		final Class<?> clazz;
		try {
			clazz = Class.forName(qualifiedName);
		} catch (final ClassNotFoundException e) {
			throw new RuntimeException(e);
		}
		return clazz;
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
	public static List<String> getFolderContentsFromClass(final Class<?> clazz) {
		if (clazz == null) {
			return null;
		}
		final ClassLoader loader = getClassLoader(clazz);
		if (loader == null) {
			return Collections.emptyList();
		}

		final String nameName = clazz.getPackage().getName();
		final String resourceName = nameName.replace(".", File.separator);

		// final URL loc = clazz.getProtectionDomain().getCodeSource().getLocation();
		//
		// try {
		// final Path dir = Paths.get(loc.toURI());
		// final Path subdir = dir.resolve(resourceName);
		// final File f = new File(subdir.toUri());
		// return Files.list(f.toPath()).map(a -> a.toString()).collect(Collectors.toList());
		// } catch (final URISyntaxException e) {
		// throw new RuntimeException(e);
		// } catch (final IOException e) {
		// throw new RuntimeException(e);
		// }

		Enumeration<URL> resourceUrlsIter = null;
		try {
			resourceUrlsIter = loader.getResources(resourceName);
		} catch (final IOException e) {
			throw new RuntimeException(e);
		}
		final List<URL> resourceUrls = new ArrayList<>();
		while (resourceUrlsIter.hasMoreElements()) {
			resourceUrls.add(resourceUrlsIter.nextElement());
		}

		final List<String> filenames = new ArrayList<>();
		for (final URL resourceUrl : resourceUrls) {
			InputStream in = null;
			try {
				in = resourceUrl.openStream();
				if (in != null) {
					final BufferedReader br = new BufferedReader(new InputStreamReader(in));
					String resource = br.readLine();
					while (resource != null) {
						filenames.add(resourceName + File.separator + resource);
						resource = br.readLine();
					}
				}
			} catch (final IOException e) {
				throw new RuntimeException(e);
			} finally {
				if (in != null) {
					try {
						in.close();
					} catch (final IOException e) {
						throw new RuntimeException(e);
					}
				}
			}
		}
		return filenames;
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

}
