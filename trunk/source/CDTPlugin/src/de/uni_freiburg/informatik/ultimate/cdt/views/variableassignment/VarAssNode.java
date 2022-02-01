/*
 * Copyright (C) 2012-2015 Stefan Wissert
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE CDTPlugin plug-in.
 * 
 * The ULTIMATE CDTPlugin plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE CDTPlugin plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE CDTPlugin plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE CDTPlugin plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE CDTPlugin plug-in grant you additional permission 
 * to convey the resulting work.
 */
/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.cdt.views.variableassignment;

import java.util.List;

/**
 * Nodes that we use inside the VariableAssignmentContentProvider
 * 
 * @author Stefan Wissert
 *
 */
public class VarAssNode {
	
	private final String name;
	private final String value;
	private List<VarAssNode> children;
	private VarAssNode parent;
	
	/**
	 * @param name
	 * @param value
	 */
	public VarAssNode(String name, String value) {
		this.name = name;
		this.value = value;
	}

	/**
	 * @return the children
	 */
	public List<VarAssNode> getChildren() {
		return children;
	}

	/**
	 * @param children the children to set
	 */
	public void setChildren(List<VarAssNode> children) {
		this.children = children;
	}

	/**
	 * @return the parent
	 */
	public VarAssNode getParent() {
		return parent;
	}

	/**
	 * @param parent the parent to set
	 */
	public void setParent(VarAssNode parent) {
		this.parent = parent;
	}

	/**
	 * @return the name
	 */
	public String getName() {
		return name;
	}

	/**
	 * @return the value
	 */
	public String getValue() {
		return value;
	}
	
}
