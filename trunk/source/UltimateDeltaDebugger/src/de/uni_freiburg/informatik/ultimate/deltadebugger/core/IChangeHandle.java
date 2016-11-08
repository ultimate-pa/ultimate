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
package de.uni_freiburg.informatik.ultimate.deltadebugger.core;

import de.uni_freiburg.informatik.ultimate.deltadebugger.core.search.minimizers.IHasSequenceIndex;

/**
 * Represents a change instance that can be independently enabled and disabled by a {@link IVariantGenerator}.
 */
public interface IChangeHandle extends IHasSequenceIndex {
	/**
	 * Returns the index of this change in the sequence of all changes.
	 * <p>
	 * This value can be used to memorize the test result for a certain subset active of changes in a more memory
	 * efficient way than by storing the list itself. Besides that, it can be used to assert that a certain subset of
	 * changes is actually a subsequence.
	 *
	 * @return index
	 */
	@Override
	int getSequenceIndex();
	
	/**
	 * @return Informative string representation for debugging purposes.
	 */
	@Override
	String toString();
}
