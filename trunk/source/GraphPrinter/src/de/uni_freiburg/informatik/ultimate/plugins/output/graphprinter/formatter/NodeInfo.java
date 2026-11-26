/*
 * Copyright (C) 2026 Manuel Bentele
 *
 * This file is part of the ULTIMATE GraphPrinter plug-in.
 *
 * The ULTIMATE GraphPrinter plug-in is free software: you can redistribute it and/or modify it under the terms of the
 * GNU Lesser General Public License as published by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE GraphPrinter plug-in is distributed in the hope that it will be useful, but WITHOUT ANY WARRANTY;
 * without even the implied warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU Lesser General
 * Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License along with the ULTIMATE GraphPrinter
 * plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7: If you modify the ULTIMATE GraphPrinter plug-in, or any
 * covered work, by linking or combining it with Eclipse RCP (or a modified version of Eclipse RCP), containing parts
 * covered by the terms of the Eclipse Public License, the licensors of the ULTIMATE GraphPrinter plug-in grant you
 * additional permission to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.plugins.output.graphprinter.formatter;

import java.util.List;

/**
 * A recursive tree data structure representing metadata extracted from graph nodes and edges.
 *
 * <p>
 * An {@link #NodeInfo} is either a <em>leaf</em> node with a name and a string value, or a <em>group</em> node with a
 * name and a list of child {@link #NodeInfo}s. This structure mirrors the tree shown in the Eclipse NodeView by
 * {@link AnnotationTreeProvider}, with sections like "IElement" (containing class name, hash code, and
 * {@code @Visualizable} fields/methods) and "Annotations" (containing payload annotations).
 * </p>
 *
 * @author Manuel Bentele
 */
public final class NodeInfo {

	private final String mName;
	private final String mValue;
	private final List<NodeInfo> mChildren;

	/**
	 * Creates a leaf node with a name and a value.
	 *
	 * @param name
	 *            The name of this entry.
	 * @param value
	 *            The string value of this entry, may be {@code null}.
	 */
	public NodeInfo(final String name, final String value) {
		mName = name;
		mValue = value;
		mChildren = List.of();
	}

	/**
	 * Creates a group node with a name and children.
	 *
	 * @param name
	 *            The name of this group.
	 * @param children
	 *            The child nodes of this group.
	 */
	public NodeInfo(final String name, final List<NodeInfo> children) {
		mName = name;
		mValue = null;
		mChildren = children != null ? List.copyOf(children) : List.of();
	}

	/**
	 * @return The name of this node.
	 */
	public String getName() {
		return mName;
	}

	/**
	 * @return The string value of this leaf node, or {@code null} if this is a group node.
	 */
	public String getValue() {
		return mValue;
	}

	/**
	 * @return The children of this group node, or an empty list if this is a leaf node.
	 */
	public List<NodeInfo> getChildren() {
		return mChildren;
	}

	/**
	 * @return {@code true} if this node has no children (i.e., is a leaf node).
	 */
	public boolean isLeaf() {
		return mChildren.isEmpty();
	}

	/**
	 * @return {@code true} if this node has children (i.e., is a group node).
	 */
	public boolean isGroup() {
		return !mChildren.isEmpty();
	}

	/**
	 * @return {@code true} if this node has a non-{@code null} value.
	 */
	public boolean hasValue() {
		return mValue != null;
	}

}
