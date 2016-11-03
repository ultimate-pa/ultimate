/*
 * Copyright (C) 2013-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 Stefan Wissert
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE BlockEncoding plug-in.
 * 
 * The ULTIMATE BlockEncoding plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE BlockEncoding plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE BlockEncoding plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE BlockEncoding plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE BlockEncoding plug-in grant you additional permission
 * to convey the resulting work.
 */
/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.blockencoding.model;

import java.util.AbstractMap.SimpleEntry;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.blockencoding.model.interfaces.IMinimizedEdge;
import de.uni_freiburg.informatik.ultimate.blockencoding.rating.interfaces.IRating;
import de.uni_freiburg.informatik.ultimate.core.lib.models.VisualizationNode;
import de.uni_freiburg.informatik.ultimate.core.model.models.IModifiableExplicitEdgesMultigraph;
import de.uni_freiburg.informatik.ultimate.core.model.models.IPayload;
import de.uni_freiburg.informatik.ultimate.core.model.models.IWalkable;
import de.uni_freiburg.informatik.ultimate.core.model.models.Payload;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.BoogieIcfgLocation;

/**
 * This is a node in our model to store all steps of the minimization. Basically we store here all steps, hence all
 * created edges, of the minimization algorithm. <br>
 * 
 * @author Stefan Wissert
 * 
 */
public class MinimizedNode implements
		IModifiableExplicitEdgesMultigraph<MinimizedNode, IMinimizedEdge, MinimizedNode, IMinimizedEdge, VisualizationNode> {

	/**
	 * Serial number, do not know if this really needed
	 */
	private static final long serialVersionUID = 1L;

	/**
	 * the reference for the underlying node in the original RCFG
	 */
	private final BoogieIcfgLocation mOriginalNode;

	/**
	 * Because we want to store all levels of the minimization, we keep in track all created edges. We store each level
	 * in this list. So the first entry of list are all basic edges. The most recent entry is the set of the most
	 * minimized edges. Every set of minimized edges is stored with an rating. Whereas the rating is the maximum rating
	 * of the complete set of minimized edges.
	 */
	private List<SimpleEntry<IRating, List<IMinimizedEdge>>> outgoingEdges;

	private List<SimpleEntry<IRating, List<IMinimizedEdge>>> incomingEdges;

	private final Payload mPayload;

	/**
	 * Constructor for the MinimizedNode, it takes as input an INode, which should always be an ProgramPoint
	 * 
	 * @param originalNode
	 *            the underlying original node (should be a ProgramPoint, since we rely on the RCFG model)
	 */
	public MinimizedNode(final BoogieIcfgLocation originalNode) {
		mOriginalNode = originalNode;
		mPayload = new Payload();
	}

	/**
	 * Getter for the underlying original node (which is a ProgramPoint)
	 * 
	 * @return the original node (ProgramPoint)
	 */
	public BoogieIcfgLocation getOriginalNode() {
		return mOriginalNode;
	}

	/**
	 * @param edges
	 */
	public void addNewOutgoingEdgeLevel(final List<IMinimizedEdge> edges, final IMinimizedEdge edgeToRate) {
		// we have to determine the maximum Rating of all edges in the list
		IRating maxRating = null;
		if (edgeToRate != null) {
			maxRating = edgeToRate.getRating();
		} else {
			for (final IMinimizedEdge edge : edges) {
				if (maxRating == null) {
					maxRating = edge.getRating();
				} else {
					if (edge.getRating().compareTo(maxRating) > 0) {
						maxRating = edge.getRating();
					}
				}
			}
		}
		if (outgoingEdges == null) {
			outgoingEdges = new ArrayList<SimpleEntry<IRating, List<IMinimizedEdge>>>();
		}
		outgoingEdges.add(new SimpleEntry<IRating, List<IMinimizedEdge>>(maxRating, edges));
	}

	/**
	 * @return
	 */
	public List<IMinimizedEdge> getMinimalOutgoingEdgeLevel() {
		if (outgoingEdges == null) {
			return null;
		}
		if (!outgoingEdges.isEmpty()) {
			return outgoingEdges.get(outgoingEdges.size() - 1).getValue();
		}
		return new ArrayList<IMinimizedEdge>();
	}

	/**
	 * @param edges
	 */
	public void addNewIncomingEdgeLevel(final List<IMinimizedEdge> edges) {
		// TODO: We need here the same, as for outgoing edge level?
		// we have to determine the maximum Rating of all edges in the list
		IRating maxRating = null;
		for (final IMinimizedEdge edge : edges) {
			if (maxRating == null) {
				maxRating = edge.getRating();
			} else {
				if (edge.getRating().compareTo(maxRating) > 0) {
					maxRating = edge.getRating();
				}
			}
		}
		if (incomingEdges == null) {
			incomingEdges = new ArrayList<SimpleEntry<IRating, List<IMinimizedEdge>>>();
		}
		incomingEdges.add(new SimpleEntry<IRating, List<IMinimizedEdge>>(maxRating, edges));
	}

	/**
	 * @return
	 */
	public List<IMinimizedEdge> getMinimalIncomingEdgeLevel() {
		if (incomingEdges == null) {
			return null;
		}
		if (!incomingEdges.isEmpty()) {
			return incomingEdges.get(incomingEdges.size() - 1).getValue();
		}
		return new ArrayList<IMinimizedEdge>();
	}

	/**
	 * @return
	 */
	public List<SimpleEntry<IRating, List<IMinimizedEdge>>> getOutgoingEdgeLevels() {
		return outgoingEdges;
	}

	/**
	 * @return
	 */
	public List<SimpleEntry<IRating, List<IMinimizedEdge>>> getIncomingEdgeLevels() {
		return incomingEdges;
	}

	@Override
	public List<IMinimizedEdge> getIncomingEdges() {
		if (incomingEdges == null) {
			return null;
		}
		return new ArrayList<IMinimizedEdge>(getMinimalIncomingEdgeLevel());
	}

	@Override
	public List<IMinimizedEdge> getOutgoingEdges() {
		if (outgoingEdges == null) {
			return null;
		}
		return new ArrayList<IMinimizedEdge>(getMinimalOutgoingEdgeLevel());
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see java.lang.Object#toString()
	 */
	@Override
	public String toString() {
		return mOriginalNode.toString();
	}

	@Override
	public IPayload getPayload() {
		return mPayload;
	}

	@Override
	public boolean hasPayload() {
		return true;
	}

	@Override
	public VisualizationNode getVisualizationGraph() {
		return new VisualizationNode(this);
	}

	@SuppressWarnings({ "unchecked", "rawtypes" })
	@Override
	public List<IWalkable> getSuccessors() {
		return (List) getOutgoingEdges();
	}

	@Override
	public boolean addIncoming(final IMinimizedEdge incoming) {
		throw new UnsupportedOperationException();
	}

	@Override
	public boolean addIncoming(final int index, final IMinimizedEdge incoming) {
		throw new UnsupportedOperationException();
	}

	@Override
	public boolean addAllIncoming(final Collection<? extends IMinimizedEdge> c) {
		throw new UnsupportedOperationException();
	}

	@Override
	public boolean addAllIncoming(final int index, final Collection<? extends IMinimizedEdge> c) {
		throw new UnsupportedOperationException();
	}

	@Override
	public void clearIncoming() {
		throw new UnsupportedOperationException();
	}

	@Override
	public IMinimizedEdge removeIncoming(final int index) {
		throw new UnsupportedOperationException();
	}

	@Override
	public boolean removeIncoming(final Object o) {
		throw new UnsupportedOperationException();
	}

	@Override
	public boolean removeAllIncoming(final Collection<?> c) {
		throw new UnsupportedOperationException();
	}

	@Override
	public boolean addOutgoing(final IMinimizedEdge outgoing) {
		throw new UnsupportedOperationException();
	}

	@Override
	public boolean addOutgoing(final int index, final IMinimizedEdge outgoing) {
		throw new UnsupportedOperationException();
	}

	@Override
	public boolean addAllOutgoing(final Collection<? extends IMinimizedEdge> c) {
		throw new UnsupportedOperationException();
	}

	@Override
	public boolean addAllOutgoing(final int index, final Collection<? extends IMinimizedEdge> c) {
		throw new UnsupportedOperationException();
	}

	@Override
	public void clearOutgoing() {
		throw new UnsupportedOperationException();
	}

	@Override
	public IMinimizedEdge removeOutgoing(final int index) {
		throw new UnsupportedOperationException();
	}

	@Override
	public boolean removeOutgoing(final Object o) {
		throw new UnsupportedOperationException();
	}

	@Override
	public boolean removeAllOutgoing(final Collection<?> c) {
		throw new UnsupportedOperationException();
	}

	@Override
	public MinimizedNode getLabel() {
		return this;
	}
}
