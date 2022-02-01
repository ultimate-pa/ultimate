/*
 * Copyright (C) 2008-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
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

package de.uni_freiburg.informatik.ultimate.core.model.observers;

import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;

/**
 * 
 * This class provides unmanaged access to the data structures of Ultimate.
 * 
 * @author dietsch
 * 
 */
public interface IUnmanagedObserver extends IObserver {

	/**
	 * Supplies a INode of a selected structure in the order determined by
	 * getWalkerOptions(). The return value determines if the walker continues
	 * to expand all the children of the given INode or not. You are free to
	 * change the supplied data structure but keep in mind that you have to obey
	 * the structural invariants of the model. Ultimate currently does not check
	 * those invariants and any break in them could cause non-termination or
	 * undesired behavior of other tools
	 * 
	 * @param root
	 *            The instance of INode which represents the root of the current
	 *            subgraph or subtree.
	 * @return true if the walker should descent to the children of the current
	 *         node, false if it should skip them.
	 * @throws Throwable iff the toolchain should be aborted 
	 */
	boolean process(IElement root) throws Throwable;
}
