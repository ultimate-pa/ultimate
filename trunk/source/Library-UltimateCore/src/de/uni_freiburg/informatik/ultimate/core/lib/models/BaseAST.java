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
package de.uni_freiburg.informatik.ultimate.core.lib.models;

import java.util.ArrayList;

import de.uni_freiburg.informatik.ultimate.core.model.models.IAST;
import de.uni_freiburg.informatik.ultimate.core.model.models.IPayload;

/***
 * Basic implementation of the {@link IAST} interface.
 * 
 * @author dietsch
 * @param <T>
 *            is the type of the concrete model. This parameter should be used by sub-classes to specify a more
 *            restrictive type and thus free clients from the need of down-casting.<br>
 *            Final implementations should fix this parameter to their type, e.g. a (fictive) type <tt>FinalModel</tt>
 *            would declare <tt>public final class FinalModel extends BaseAST&lt;FinalModel&gt;</tt> .
 * @see IAST
 * @see BaseSimpleAST
 * 
 */
public abstract class BaseAST<T extends IAST<T, VisualizationNode>> extends BaseSimpleAST<T>
		implements IAST<T, VisualizationNode> {

	/**
	 * ID to distinguish different versions of this class. If the class gains additional fields, this constant should be
	 * incremented. This field may not be renamed.
	 */
	private static final long serialVersionUID = 1L;

	protected T mParent;

	/**
	 * This constructor creates a BaseAST node without a parent and without payload.
	 */
	protected BaseAST() {
		this(null, null);
	}

	/**
	 * This constructor creates a BaseAST node without a parent but with a given payload.
	 * 
	 * @param payload
	 *            A new payload or null.
	 */
	protected BaseAST(IPayload payload) {
		this(null, payload);

	}

	/**
	 * This constructor creates a BaseAST node with a given parent but without a payload.
	 * 
	 * @param parent
	 */
	protected BaseAST(T parent) {
		this(parent, null);
	}

	/**
	 * This construtor creates a BaseAST node with a given parent and a given payload. If the parent is not null, this
	 * node will be added to the parent's list of children.
	 * 
	 * @param parent
	 *            A parent node or null.
	 * @param payload
	 *            A new payload or null.
	 */
	@SuppressWarnings("unchecked")
	protected BaseAST(T parent, IPayload payload) {
		super(payload);
		mOutgoingNodes = new ArrayList<T>();
		if (parent != null) {
			mParent = parent;
			parent.getOutgoingNodes().add((T) this);
		}
	}

	@Override
	public T getIncomingNode() {
		return mParent;
	}

}
