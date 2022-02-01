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
package de.uni_freiburg.informatik.ultimate.deltadebugger.core.search.minimizers;

import java.util.List;

/**
 * Represents an iterative minimization algorithm.
 *
 * @see IMinimizerStep
 */
public interface IMinimizer {
	/**
	 * Create the initial algorithm state to minimize the given input sequence.
	 *
	 * @param input
	 *            input sequence
	 * @param <E>
	 *            element type
	 * @return initial algorithm state
	 */
	<E> IMinimizerStep<E> create(List<E> input);
	
	/**
	 * @return Whether duplicate variants may be generated or not.
	 */
	boolean isEachVariantUnique();
	
	/**
	 * Returns whether the result is a local minimum wrt. this minimizer. This flag tell whether applying the same
	 * minimizer again may result in a further reduction or not. It does not mean the result is a globally minimal and
	 * not even one-minimal.
	 *
	 * @return whether the result is locally minimal or not
	 */
	boolean isResultMinimal();
}
