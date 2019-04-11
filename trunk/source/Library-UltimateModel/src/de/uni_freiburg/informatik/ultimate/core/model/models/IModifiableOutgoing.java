/*
 * Copyright (C) 2012-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
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
package de.uni_freiburg.informatik.ultimate.core.model.models;

import java.util.Collection;

//TODO Add comments (DD)
public interface IModifiableOutgoing<T> {
	// TODO Add comments (DD)
	boolean addOutgoing(T outgoing);

	// TODO Add comments (DD)
	// TODO Optional operation
	boolean addOutgoing(int index, T outgoing);
	
	// TODO Add comments (DD)
	boolean addAllOutgoing(Collection<? extends T> c);

	// TODO Add comments (DD)
	// TODO Optional operation
	boolean addAllOutgoing(int index, Collection<? extends T> c);

	// TODO Add comments (DD)
	void clearOutgoing();

	// TODO Add comments (DD)
	T removeOutgoing(int index);

	// TODO Add comments (DD)
	boolean removeOutgoing(T o);

	// TODO Add comments (DD)
	boolean removeAllOutgoing(Collection<? extends T> c);
}
