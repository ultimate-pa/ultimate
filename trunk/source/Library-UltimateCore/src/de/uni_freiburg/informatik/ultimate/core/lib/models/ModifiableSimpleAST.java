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
package de.uni_freiburg.informatik.ultimate.core.lib.models;

import java.util.Collection;

import de.uni_freiburg.informatik.ultimate.core.model.models.IModifiableSimpleAST;
import de.uni_freiburg.informatik.ultimate.core.model.models.IPayload;
import de.uni_freiburg.informatik.ultimate.core.model.models.ISimpleAST;

/***
 * This class provides a basic implementation for {@link IModifiableSimpleAST}. It uses the standard list operations to
 * provide modifications to the list of successor nodes of {@link ISimpleAST}.
 * 
 * @author dietsch
 * @see IModifiableSimpleAST
 * 
 */
public abstract class ModifiableSimpleAST<T extends IModifiableSimpleAST<T, VisualizationNode>> extends BaseSimpleAST<T>
		implements IModifiableSimpleAST<T, VisualizationNode> {

	/**
	 * ID to distinguish different versions of this class. If the class gains additional fields, this constant should be
	 * incremented. This field may not be renamed.
	 */
	private static final long serialVersionUID = 1L;

	/**
	 * This constructor creates a {@link ModifiableSimpleAST} without a payload.
	 */
	protected ModifiableSimpleAST() {
		this(null);
	}

	/**
	 * This constructor creates a {@link ModifiableSimpleAST} with a given payload.
	 * 
	 * @param payload
	 *            A payload for the new {@link ModifiableSimpleAST} node or null.
	 */
	protected ModifiableSimpleAST(IPayload payload) {
		super(payload);
	}

	/* ---------- IModifiableSimpleAST implementation ---------- */

	@Override
	public boolean addOutgoing(T successorNode) {
		return mOutgoingNodes.add(successorNode);
	}

	@Override
	public boolean addAllOutgoing(Collection<? extends T> c) {
		return mOutgoingNodes.addAll(c);
	}

	@Override
	public boolean addAllOutgoing(int index, Collection<? extends T> c) {
		return mOutgoingNodes.addAll(index, c);
	}

	@Override
	public void clearOutgoing() {
		mOutgoingNodes.clear();
	}

	@Override
	public T removeOutgoing(int index) {
		return mOutgoingNodes.remove(index);
	}

	@Override
	public boolean removeOutgoing(T o) {
		return mOutgoingNodes.remove(o);
	}

	@Override
	public boolean removeAllOutgoing(Collection<? extends T> c) {
		return mOutgoingNodes.removeAll(c);
	}

	@Override
	public boolean addOutgoing(int index, T outgoing) {
		final int size = mOutgoingNodes.size();
		mOutgoingNodes.add(index, outgoing);
		return size != mOutgoingNodes.size();
	}

}
