/*
 * Copyright (C) 2009-2026 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.smtinterpol.convert;

/**
 * Interface used for non-recursive pattern in Clausifier. It differs from
 * logic.NonRecursive by not having a reference to the engine and not having
 * functions specific to terms.
 *
 * The idea is that operations are queued on a stack to avoid recursion. The
 * main loop in clausifier runs all operations until the stack is empty. An
 * operation can queue a new operation instead of recursively executing it
 * directly.
 */
interface Operation {
	/**
	 * Perform the queued operation.
	 */
	public void perform();
}