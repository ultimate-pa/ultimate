/*
 * Copyright (C) 2026 University of Freiburg
 *
 * This file is part of the ULTIMATE SwtVisualization plug-in.
 *
 * The ULTIMATE SwtVisualization plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE SwtVisualization plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE SwtVisualization plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE SwtVisualization plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE SwtVisualization plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.output.swtvisualization.editor;

import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;

import org.eclipse.jface.resource.ImageDescriptor;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.IPersistableElement;

import de.uni_freiburg.informatik.ultimate.core.lib.models.VisualizationEdge;
import de.uni_freiburg.informatik.ultimate.core.lib.models.VisualizationNode;

/**
 * EditorInput for the {@link SwtEditor}. Holds the graph data (root node, all nodes, all edges, error traces).
 */
public class SwtEditorInput implements IEditorInput {

	private final String mName;
	private final VisualizationNode mRootNode;
	private final List<VisualizationNode> mNodes;
	private final List<VisualizationEdge> mEdges;
	private final List<LinkedHashSet<Object>> mErrorTraces;

	public SwtEditorInput(final String name, final VisualizationNode rootNode,
			final List<VisualizationNode> nodes, final List<VisualizationEdge> edges,
			final List<LinkedHashSet<Object>> errorTraces) {
		mName = name;
		mRootNode = rootNode;
		mNodes = new ArrayList<>(nodes);
		mEdges = new ArrayList<>(edges);
		mErrorTraces = new ArrayList<>(errorTraces);
	}

	public VisualizationNode getRootNode() {
		return mRootNode;
	}

	public List<VisualizationNode> getNodes() {
		return mNodes;
	}

	public List<VisualizationEdge> getEdges() {
		return mEdges;
	}

	public List<LinkedHashSet<Object>> getErrorTraces() {
		return mErrorTraces;
	}

	public boolean isCounterExampleEdge(final VisualizationEdge edge) {
		final Object backing = edge.getBacking();
		if (backing == null) {
			return false;
		}
		for (final LinkedHashSet<Object> trace : mErrorTraces) {
			if (trace.contains(backing)) {
				return true;
			}
		}
		return false;
	}

	/**
	 * Checks if the given node is an error location, i.e., the target of the last edge in any error trace.
	 *
	 * @param node
	 *            The {@link VisualizationNode} to check.
	 * @return {@code true} if the node's backing element is the last element of an error trace.
	 */
	public boolean isErrorLocation(final VisualizationNode node) {
		if (mErrorTraces.isEmpty()) {
			return false;
		}
		final Object backing = node.getBacking();
		if (backing == null) {
			return false;
		}
		for (final LinkedHashSet<Object> trace : mErrorTraces) {
			// The last element in the trace is the error location
			Object last = null;
			for (final Object elem : trace) {
				last = elem;
			}
			if (backing.equals(last)) {
				return true;
			}
		}
		return false;
	}

	@Override
	public boolean exists() {
		return false;
	}

	@Override
	public ImageDescriptor getImageDescriptor() {
		return null;
	}

	@Override
	public String getName() {
		return mName;
	}

	@Override
	public IPersistableElement getPersistable() {
		return null;
	}

	@Override
	public String getToolTipText() {
		return "SWT Graph View: " + mName;
	}

	@SuppressWarnings("rawtypes")
	@Override
	public Object getAdapter(final Class adapter) {
		return null;
	}
}
