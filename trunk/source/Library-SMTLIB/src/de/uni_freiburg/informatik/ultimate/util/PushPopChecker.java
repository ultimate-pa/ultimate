/*
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of SMTInterpol.
 *
 * SMTInterpol is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * SMTInterpol is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with SMTInterpol.  If not, see <http://www.gnu.org/licenses/>.
 */
package de.uni_freiburg.informatik.ultimate.util;

import de.uni_freiburg.informatik.ultimate.logic.Script;

public final class PushPopChecker {
	private PushPopChecker() {
		// Prevent initialization of helper class.
	}
	/**
	 * Returns the current assertion stack level of the given script.  This
	 * uses an info flag that is present for a while now in SMTInterpol but is
	 * only standardized since SMTLIB 2.5.  Since this info flag is optional,
	 * it might not be supported.  In this case, this function returns -1.
	 * @param script The script to check for an assertion stack level.
	 * @return The current assertion stack level, or -1 if the script does not
	 *         provide this information.
	 */
	public static int currentLevel(Script script) {
		try {
			final Object lvl = script.getInfo(":assertion-stack-levels");
			if (lvl instanceof Number) {
				return ((Number) lvl).intValue();
			}
		} catch (final UnsupportedOperationException eNotSupp) {
			// we ignore unsupported and return -1;
		}
		return -1;
	}
	/**
	 * Check if a script is at a given assertion stack level.  No special care
	 * is taken if the script does not provide information about assertion stack
	 * level.  In this case, -1 is expected as level (see
	 * {@link #currentLevel(Script)}).
	 * @param script The script to check.
	 * @param lvl    The expected assertion stack level (-1 if script does not
	 *               provide this information)
	 * @return Is the script at the given assertion stack level?
	 */
	public static boolean atLevel(Script script, int lvl) {
		return currentLevel(script) == lvl;
	}
}
