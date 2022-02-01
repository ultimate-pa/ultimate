/*
 * Copyright (C) 2016 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
 *
 * This file is part of the ULTIMATE CLI plug-in.
 *
 * The ULTIMATE CLI plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE CLI plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE CLI plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE CLI plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE CLI plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.core.coreplugin.exceptions;

/**
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class UncheckedURISyntaxException extends RuntimeException {

	private static final long serialVersionUID = 1L;

	/**
	 * Create an {@link UncheckedURISyntaxException} exception.
	 *
	 * @param message
	 *            a message detailing why this exception was thrown.
	 */
	public UncheckedURISyntaxException(final String message) {
		super(message);
	}

	/**
	 * Create an {@link UncheckedURISyntaxException} exception.
	 *
	 * @param message
	 *            a message detailing why this exception was thrown.
	 * @param cause
	 *            an earlier exception that lead to this exception.
	 */
	public UncheckedURISyntaxException(final String message, final Exception cause) {
		super(message, cause);
	}

	/**
	 * Create an {@link UncheckedURISyntaxException} exception.
	 *
	 * @param cause
	 *            an earlier exception that lead to this exception.
	 */
	public UncheckedURISyntaxException(final Exception cause) {
		super(cause);
	}
}
