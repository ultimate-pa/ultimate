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
/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.core.coreplugin;

import java.io.Serializable;

import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.models.IWalkable;
import de.uni_freiburg.informatik.ultimate.core.model.models.ModelType;

/**
 * This class is the general model container. It should preselect walkers and
 * perform a number of search operations on its model.
 * 
 * @author dietsch
 * @version 0.0.2
 */
public class ModelContainer implements Serializable {

	/**
	 * long serialVersionUID
	 */
	private static final long serialVersionUID = -1957760572620128974L;

	private IElement mGraphRoot;

	private ModelType mGraphType;

	private String mGraphName;

	protected ModelContainer(IElement rootNode, ModelType type, String name) {
		mGraphRoot = rootNode;
		mGraphType = type;
		mGraphName = name;
		init();
	}

	protected IElement getRoot() {
		return mGraphRoot;
	}

	protected String getName() {
		return mGraphName;
	}

	protected int getSize() {
		return -1;
	}

	public String toString() {
		return mGraphType.toString();
	}

	protected ModelType getType() {
		return mGraphType;
	}

	private void init() {
		mGraphType.setSize(countNodes(this.mGraphRoot));
	}

	protected void cleanup() {
	}

	private int countNodes(IElement root) {
		return 0;
	}

	/**
	 * Finds Nodes based on their annotations. Expects every parameter to be not
	 * null! Simple recursive depth-first search.
	 * 
	 * @param outerAnnotationKey
	 * @param innerAnnotationKey
	 * @param innerAnnotationValue
	 * @param node
	 * @return Node with given annotation.
	 */
	protected static IElement findNode(String outerAnnotationKey,
			String innerAnnotationKey, Object innerAnnotationValue,
			IElement node) {
		// TODO implement search with support for null values (perhaps even
		// nodesets as return values
		if (node.getPayload().getAnnotations().get(outerAnnotationKey)
				.getAnnotationsAsMap().get(innerAnnotationKey)
				.equals(innerAnnotationValue)) {
			return node;
		} else {
			if (node instanceof IWalkable) {
				IElement returnNode = null;
				for (IElement i : ((IWalkable) node).getSuccessors()) {
					returnNode = findNode(outerAnnotationKey,
							innerAnnotationKey, innerAnnotationValue, i);
					if (returnNode != null) {
						return returnNode;
					}
				}
			}
		}
		return null;
	}
}
