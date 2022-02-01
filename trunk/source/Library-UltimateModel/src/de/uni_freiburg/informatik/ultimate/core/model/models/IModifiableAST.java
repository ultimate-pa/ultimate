/*
 * Copyright (C) 2013-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
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

/***
 * This interface represents a modifiable variant of {@link IAST}.
 * 
 * @author dietsch
 * 
 * @param <T>
 *            is the type of the concrete model. This parameter should be used by sub-interfaces to specify a more
 *            restrictive type and thus free clients from the need of down-casting.<br>
 *            Final implementations should fix this parameter to their type, e.g. a (fictive) type <tt>FinalModel</tt>
 *            would declare <tt>public final class FinalModel implements IModifiableAST&lt;FinalModel&gt;</tt> .
 * @see IAST
 * @see IModifiableOutgoing
 */
public interface IModifiableAST<T extends IModifiableAST<T, E>, E extends IVisualizable<E>>
		extends IAST<T, E>, IModifiableOutgoing<T> {

	/**
	 * This method changes the parent pointer of the current node. This operation may break the link between children
	 * and parent by removing or changing the parent pointer but retaining the child in the parents
	 * {@link ISimpleAST#getOutgoingNodes getOutgoingNodes()} list.
	 * 
	 * @param parent
	 *            A new parent node or null.
	 */
	void setIncomingNode(T parent);

	/**
	 * This method changes the parent pointer of the given node. This operation retains the invariants of IAST by
	 * automatically removing the current node from the {@link ISimpleAST#getOutgoingNodes list of children} of the old
	 * parent and inserting it into the list of children of the new parent. If the new parent is null, the operation
	 * will only remove the current node from the list of children of the old parent.
	 * 
	 * @param parent
	 *            A new parent or null.
	 */
	void redirectParent(T parent);
}
