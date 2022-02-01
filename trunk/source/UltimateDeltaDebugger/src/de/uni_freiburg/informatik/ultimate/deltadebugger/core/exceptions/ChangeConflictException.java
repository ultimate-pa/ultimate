/*
 * Copyright (C) 2016 University of Freiburg
 *
 * This file is part of the Ultimate Delta Debugger plug-in.
 *
 * The Ultimate Delta Debugger plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The Ultimate Delta Debugger plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the Ultimate Delta Debugger plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the Ultimate Delta Debugger plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the Ultimate Delta Debugger plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.deltadebugger.core.exceptions;

/**
 * Thrown to indicate that one or more changes could not be applied. The caller can continue to generate other
 * variants, just this particular combination of changes is not possible to apply.
 */
public class ChangeConflictException extends RuntimeException {
	private static final long serialVersionUID = 1L;
	
	/**
	 * Default constructor.
	 */
	public ChangeConflictException() {
		super();
	}
	
	/**
	 * @param message
	 *            Message.
	 */
	public ChangeConflictException(final String message) {
		super(message);
	}
	
	/**
	 * @param message
	 *            Message.
	 * @param cause
	 *            cause
	 */
	public ChangeConflictException(final String message, final Throwable cause) {
		super(message, cause);
	}
	
	/**
	 * @param message
	 *            Message.
	 * @param cause
	 *            cause
	 * @param enableSuppression
	 *            {@code true} iff suppression is enabled
	 * @param writableStackTrace
	 *            {@code true} iff stack trace should be written
	 */
	public ChangeConflictException(final String message, final Throwable cause, final boolean enableSuppression,
			final boolean writableStackTrace) {
		super(message, cause, enableSuppression, writableStackTrace);
	}
	
	/**
	 * @param cause
	 *            Cause.
	 */
	public ChangeConflictException(final Throwable cause) {
		super(cause);
	}
}
