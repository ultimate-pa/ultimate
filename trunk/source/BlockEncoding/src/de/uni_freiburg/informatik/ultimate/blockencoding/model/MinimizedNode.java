/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.blockencoding.model;

import java.util.AbstractMap.SimpleEntry;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.blockencoding.model.interfaces.IMinimizedEdge;
import de.uni_freiburg.informatik.ultimate.blockencoding.model.interfaces.IRating;
import de.uni_freiburg.informatik.ultimate.model.IPayload;
import de.uni_freiburg.informatik.ultimate.model.Payload;
import de.uni_freiburg.informatik.ultimate.model.structure.IModifiableExplicitEdgesMultigraph;
import de.uni_freiburg.informatik.ultimate.model.structure.IWalkable;
import de.uni_freiburg.informatik.ultimate.model.structure.VisualizationNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;

/**
 * This is a node in our model to store all steps of the minimization. Basically
 * we store here all steps, hence all created edges, of the minimization
 * algorithm. <br>
 * 
 * @author Stefan Wissert
 * 
 */
public class MinimizedNode implements
		IModifiableExplicitEdgesMultigraph<MinimizedNode, IMinimizedEdge> {

	/**
	 * Serial number, do not know if this really needed
	 */
	private static final long serialVersionUID = 1L;

	/**
	 * the reference for the underlying node in the original RCFG
	 */
	private ProgramPoint originalNode;

	/**
	 * Because we want to store all levels of the minimization, we keep in track
	 * all created edges. We store each level in this list. So the first entry
	 * of list are all basic edges. The most recent entry is the set of the most
	 * minimized edges. Every set of minimized edges is stored with an rating.
	 * Whereas the rating is the maximum rating of the complete set of minimized
	 * edges.
	 */
	private List<SimpleEntry<IRating, List<IMinimizedEdge>>> outgoingEdges;

	private List<SimpleEntry<IRating, List<IMinimizedEdge>>> incomingEdges;

	private Payload payload;

	/**
	 * Constructor for the MinimizedNode, it takes as input an INode, which
	 * should always be an ProgramPoint
	 * 
	 * @param originalNode
	 *            the underlying original node (should be a ProgramPoint, since
	 *            we rely on the RCFG model)
	 */
	public MinimizedNode(ProgramPoint originalNode) {
		this.originalNode = originalNode;
		this.payload = new Payload();
		this.payload.setName(this.originalNode.toString());
	}

	/**
	 * Getter for the underlying original node (which is a ProgramPoint)
	 * 
	 * @return the original node (ProgramPoint)
	 */
	public ProgramPoint getOriginalNode() {
		return originalNode;
	}

	/**
	 * @param edges
	 */
	public void addNewOutgoingEdgeLevel(List<IMinimizedEdge> edges) {
		// we have to determine the maximum Rating of all edges in the list
		IRating maxRating = null;
		for (IMinimizedEdge edge : edges) {
			if (maxRating == null) {
				maxRating = edge.getRating();
			} else {
				if (edge.getRating().compareTo(maxRating) > 0) {
					maxRating = edge.getRating();
				}
			}
		}
		if (this.outgoingEdges == null) {
			this.outgoingEdges = new ArrayList<SimpleEntry<IRating, List<IMinimizedEdge>>>();
		}
		this.outgoingEdges.add(new SimpleEntry<IRating, List<IMinimizedEdge>>(
				maxRating, edges));
	}

	/**
	 * @return
	 */
	public List<IMinimizedEdge> getMinimalOutgoingEdgeLevel() {
		if (this.outgoingEdges == null) {
			return null;
		}
		if (this.outgoingEdges.size() > 0) {
			return this.outgoingEdges.get(this.outgoingEdges.size() - 1)
					.getValue();
		}
		return new ArrayList<IMinimizedEdge>();
	}

	/**
	 * @param edges
	 */
	public void addNewIncomingEdgeLevel(List<IMinimizedEdge> edges) {
		// we have to determine the maximum Rating of all edges in the list
		IRating maxRating = null;
		for (IMinimizedEdge edge : edges) {
			if (maxRating == null) {
				maxRating = edge.getRating();
			} else {
				if (edge.getRating().compareTo(maxRating) > 0) {
					maxRating = edge.getRating();
				}
			}
		}
		if (this.incomingEdges == null) {
			this.incomingEdges = new ArrayList<SimpleEntry<IRating, List<IMinimizedEdge>>>();
		}
		this.incomingEdges.add(new SimpleEntry<IRating, List<IMinimizedEdge>>(
				maxRating, edges));
	}

	/**
	 * @return
	 */
	public List<IMinimizedEdge> getMinimalIncomingEdgeLevel() {
		if (this.incomingEdges == null) {
			return null;
		}
		if (this.incomingEdges.size() > 0) {
			return this.incomingEdges.get(this.incomingEdges.size() - 1)
					.getValue();
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
		if (this.incomingEdges == null) {
			return null;
		}
		return new ArrayList<IMinimizedEdge>(getMinimalIncomingEdgeLevel());
	}

	@Override
	public List<IMinimizedEdge> getOutgoingEdges() {
		if (this.outgoingEdges == null) {
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
		return this.originalNode.toString();
	}

	@Override
	public IPayload getPayload() {
		return this.payload;
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
		return (List<IWalkable>) (List) getOutgoingEdges();
	}

	@Override
	public boolean addIncoming(IMinimizedEdge incoming) {
		throw new UnsupportedOperationException();
	}

	@Override
	public boolean addIncoming(int index, IMinimizedEdge incoming) {
		throw new UnsupportedOperationException();
	}

	@Override
	public boolean addAllIncoming(Collection<? extends IMinimizedEdge> c) {
		throw new UnsupportedOperationException();
	}

	@Override
	public boolean addAllIncoming(int index,
			Collection<? extends IMinimizedEdge> c) {
		throw new UnsupportedOperationException();
	}

	@Override
	public void clearIncoming() {
		throw new UnsupportedOperationException();
	}

	@Override
	public IMinimizedEdge removeIncoming(int index) {
		throw new UnsupportedOperationException();
	}

	@Override
	public boolean removeIncoming(Object o) {
		throw new UnsupportedOperationException();
	}

	@Override
	public boolean removeAllIncoming(Collection<?> c) {
		throw new UnsupportedOperationException();
	}

	@Override
	public boolean addOutgoing(IMinimizedEdge outgoing) {
		throw new UnsupportedOperationException();
	}

	@Override
	public boolean addOutgoing(int index, IMinimizedEdge outgoing) {
		throw new UnsupportedOperationException();
	}

	@Override
	public boolean addAllOutgoing(Collection<? extends IMinimizedEdge> c) {
		throw new UnsupportedOperationException();
	}

	@Override
	public boolean addAllOutgoing(int index,
			Collection<? extends IMinimizedEdge> c) {
		throw new UnsupportedOperationException();
	}

	@Override
	public void clearOutgoing() {
		throw new UnsupportedOperationException();
	}

	@Override
	public IMinimizedEdge removeOutgoing(int index) {
		throw new UnsupportedOperationException();
	}

	@Override
	public boolean removeOutgoing(Object o) {
		throw new UnsupportedOperationException();
	}

	@Override
	public boolean removeAllOutgoing(Collection<?> c) {
		throw new UnsupportedOperationException();
	}
}
