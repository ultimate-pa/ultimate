/*
 * Copyright (C) 2015 Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE SpaceExParser plug-in.
 * 
 * The ULTIMATE SpaceExParser plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE SpaceExParser plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE SpaceExParser plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE SpaceExParser plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE SpaceExParser plug-in grant you additional permission 
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.plugins.spaceex.ast;

import de.uni_freiburg.informatik.ultimate.core.lib.models.ModifiableExplicitEdgesMultigraph;

/**
 * Represents the root node of a SpaceEx model AST parsed from any given SpaceEx model file.
 * 
 * @author greitsch@informatik.uni-freiburg.de
 *
 */
public abstract class SpaceExNode
        extends ModifiableExplicitEdgesMultigraph<SpaceExNode, SpaceExModelEdge, SpaceExNode, SpaceExModelEdge> {

	/**
	 * This field holds the name of the current node.
	 */
	private String mName;

	/**
	 * Serialization ID.
	 */
	private static final long serialVersionUID = 1L;

	/**
	 * Creates a new instance of a SpaceEx Root Node.
	 */
	public SpaceExNode() {
		mName = "SpaceExRoot";
	}

	public final void setName(String name) {
		mName = name;
	}

	public final String getName() {
		return mName;
	}

	@Override
	public String toString() {
		return mName;
	}

	@Override
	public SpaceExNode getLabel() {
		return this;
	}

}
