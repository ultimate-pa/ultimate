/*
 * Copyright (C) 2015-2016 Christian Schilling (schillic@informatik.uni-freiburg.de)
 * Copyright (C) 2015-2016 University of Freiburg
 * 
 * This file is part of the ULTIMATE Automaton Delta Debugger.
 * 
 * The ULTIMATE Automaton Delta Debugger is free software: you can redistribute
 * it and/or modify it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation, either version 3 of the
 * License, or (at your option) any later version.
 * 
 * The ULTIMATE Automaton Delta Debugger is distributed in the hope that it will
 * be useful, but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU Lesser
 * General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Automaton Delta Debugger. If not, see
 * <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7: If you modify the
 * ULTIMATE Automaton Delta Debugger, or any covered work, by linking or
 * combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Automaton Delta Debugger grant you additional
 * permission to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.analysis.automatondeltadebugger.core;

/**
 * Fresh exception type for the debugger.
 * <p>
 * In order to prevent several causes for the designated error, this exception can be thrown at the respective position
 * to make sure the debugger looks for the correct error position. Of course, a user can specify new types of exceptions
 * as well.
 * <p>
 * NOTE: After debugging the exception should be removed again, so that the invariant that this exception is thrown at
 * most once in the whole library holds.
 * 
 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
 */
public class DebuggerException extends Exception {
	private static final long serialVersionUID = 1L;

	private final Class<?> mClassOfThrower;
	private final String mMessage;

	/**
	 * @param thrower
	 *            Class of the thrower (for better identification).
	 * @param message
	 *            message to print when throwing
	 */
	public DebuggerException(final Class<?> thrower, final String message) {
		mClassOfThrower = thrower;
		mMessage = message;
	}

	/**
	 * @param message
	 *            Message to print when throwing.
	 */
	public DebuggerException(final String message) {
		mClassOfThrower = null;
		mMessage = message;
	}

	@Override
	public String toString() {
		final StringBuilder builder = new StringBuilder();
		// @formatter:off
		builder.append(getClass().getSimpleName())
				.append('(')
				.append(mClassOfThrower == null ? "null" : mClassOfThrower.toString())
				.append(" : ")
				.append(mMessage)
				.append(')');
		// @formatter:on
		return builder.toString();
	}
}
