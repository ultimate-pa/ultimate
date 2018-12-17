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

	public static String getCallerMethodName(final int callStackDepth) {
		final StackTraceElement[] callStack = Thread.currentThread().getStackTrace();
		if (callStack.length < callStackDepth) {
			return callStack[callStack.length - 1].getMethodName();
		}
		return callStack[callStackDepth].getMethodName();
	}

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
	 * A custom security manager that exposes the getClassContext() information
	 */
	private static final class ExposedSecurityManager extends SecurityManager {
		public Class<?> getCallerClass(final int callStackDepth) {
			return getClassContext()[callStackDepth];
		}
	}

}
