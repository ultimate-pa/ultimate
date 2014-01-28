package de.uni_freiburg.informatik.ultimate.model.structure;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.core.coreplugin.Activator;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.IOutput;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.model.IPayload;

/***
 * VisualizationNode is the Ultimate model for graph visualizations. It wraps
 * every other graph structure and provides a unified interface for
 * {@link IOutput} plugins through the {@link IVisualizable} interface.
 * 
 * In general, each {@link IVisualizable} type has a corresponding constructor
 * in this class that creates a anonymous sub-class of the inner class
 * WrapperNode which builds a visualization structure through lazy
 * initialization. This visualization structure corresponds to a directed
 * multigraph described through {@link IExplicitEdgesMultigraph}. The
 * corresponding edge type is {@link VisualizationEdge}.
 * 
 * Please note that the resulting visualization structure can be larger than the
 * original graph structure, as cycles may lead to multiple WrapperNodes for a
 * single original node (same for edges).
 * 
 * {@link IOutput} implementations have to ensure that they always use the
 * {@link VisualizationNode#equals(Object)} and {@link VisualizationEdge}
 * {@link #equals(Object)} methods to compare instances of those structures, as
 * they will return true if the backing is the same for two different instances.
 * 
 * @author dietsch
 * @see VisualizationEdge
 * @see IExplicitEdgesMultigraph
 */
public final class VisualizationNode implements
		IExplicitEdgesMultigraph<VisualizationNode, VisualizationEdge> {

	private static final long serialVersionUID = 1L;

	private final VisualizationWrapperNode mBacking;
	private List<VisualizationNode> mOutgoing;

	public VisualizationNode(final IExplicitEdgesMultigraph<?, ?> node) {
		mBacking = new VisualizationWrapperNode(node) {

			@Override
			protected void createIncoming() {
				for (IMultigraphEdge<?, ?> e : node.getIncomingEdges()) {
					if (e.getSource() != null) {
						VisualizationEdge ve;
						if (e.hasPayload()) {
							ve = new VisualizationEdge(e.getSource()
									.getVisualizationGraph(),
									VisualizationNode.this, e.getPayload(), e);
						} else {
							ve = new VisualizationEdge(e.getSource()
									.getVisualizationGraph(),
									VisualizationNode.this, e);
						}
						mIncoming.add(ve);
					}
				}
			}

			@Override
			protected void createOutgoing() {
				for (IMultigraphEdge<?, ?> e : node.getOutgoingEdges()) {
					if (e.getTarget() != null) {
						VisualizationEdge ve;
						if (e.hasPayload()) {
							ve = new VisualizationEdge(VisualizationNode.this,
									e.getTarget().getVisualizationGraph(),
									e.getPayload(), e);
						} else {
							ve = new VisualizationEdge(VisualizationNode.this,
									e.getTarget().getVisualizationGraph(), e);
						}
						mOutgoing.add(ve);
					}
				}

			}

			@SuppressWarnings({ "unchecked", "rawtypes" })
			@Override
			protected List<IWalkable> getSuccessors() {
				return (List<IWalkable>) (List) getOutgoingEdges();
			}
		};

	}

	public <T extends ILabeledEdgesMultigraph<T, L>, L> VisualizationNode(
			final ILabeledEdgesMultigraph<T, L> node) {
		// TODO: We need to handle the case where L is an instance of an
		// collection (i.e. multigraph)
		mBacking = new VisualizationWrapperNode(node) {

			private IPayload extractPayload(L label) {
				IPayload pay = null;
				if (label instanceof IPayload) {
					pay = (IPayload) label;
				} else if (label instanceof IElement) {
					IElement ele = (IElement) label;
					if (ele.hasPayload()) {
						pay = ele.getPayload();
					}
				}
				return pay;
			}

			@SuppressWarnings("unchecked")
			@Override
			protected void createIncoming() {
				for (ILabeledEdgesMultigraph<T, L> pred : node
						.getIncomingNodes()) {
					VisualizationEdge ve;
					IPayload pay = extractPayload(node
							.getIncomingEdgeLabel((T) pred));

					if (pay != null) {
						ve = new VisualizationEdge(
								pred.getVisualizationGraph(),
								VisualizationNode.this, pay, null);
					} else {
						ve = new VisualizationEdge(
								pred.getVisualizationGraph(),
								VisualizationNode.this, null);
					}
					mIncoming.add(ve);
				}

			}

			@SuppressWarnings("unchecked")
			@Override
			protected void createOutgoing() {
				for (ILabeledEdgesMultigraph<T, L> succ : node
						.getOutgoingNodes()) {
					VisualizationEdge ve;
					IPayload pay = extractPayload(node
							.getOutgoingEdgeLabel((T) succ));

					if (pay != null) {
						ve = new VisualizationEdge(VisualizationNode.this,
								succ.getVisualizationGraph(), pay, null);
					} else {
						ve = new VisualizationEdge(

						VisualizationNode.this, succ.getVisualizationGraph(),
								null);
					}
					mOutgoing.add(ve);
				}

			}

			@Override
			protected List<IWalkable> getSuccessors() {
				ArrayList<IWalkable> rtr = new ArrayList<IWalkable>();
				for (ILabeledEdgesMultigraph<T, L> succ : node
						.getOutgoingNodes()) {
					final ILabeledEdgesMultigraph<T, L> child = succ;
					rtr.add(new IWalkable() {

						private static final long serialVersionUID = 1L;

						@SuppressWarnings("unchecked")
						@Override
						public boolean hasPayload() {
							return extractPayload(node
									.getOutgoingEdgeLabel((T) child)) != null;
						}

						@SuppressWarnings("unchecked")
						@Override
						public IPayload getPayload() {
							return extractPayload(node
									.getOutgoingEdgeLabel((T) child));
						}

						@Override
						public List<IWalkable> getSuccessors() {
							return Collections.singletonList((IWalkable) child);
						}
					});
				}
				return rtr;
			}
		};
	}

	public VisualizationNode(final ISimpleAST<?> node) {
		mBacking = new VisualizationWrapperNode(node) {

			@SuppressWarnings({ "unchecked", "rawtypes" })
			@Override
			protected List<IWalkable> getSuccessors() {
				return (List<IWalkable>) (List) getOutgoingEdges();
			}

			@Override
			protected void createOutgoing() {
				// we also create the incoming edge for this tree if we traverse
				// in the right order
				mIncoming = new ArrayList<VisualizationEdge>();

				for (ISimpleAST<?> succ : node.getOutgoingNodes()) {
					if (succ == null) {
						continue;
					}
					VisualizationEdge ve;
					if (succ.hasPayload()) {
						ve = new VisualizationEdge(VisualizationNode.this,
								succ.getVisualizationGraph(),
								succ.getPayload(), succ);
					} else {
						ve = new VisualizationEdge(VisualizationNode.this,
								succ.getVisualizationGraph(), succ);
					}
					mOutgoing.add(ve);
					// succ.getVisualizationGraph().getIncomingEdges().add(ve);
				}
			}

			@Override
			protected void createIncoming() {
				// we only warn here, because after a call to getOutgoingEdges
				// the incomingEdges should be initialized
				// mLogger.warn("ISimpleAST does not support parent pointer -- try calling getOutgoingEdges() first");
			}
		};
	}

	public VisualizationNode(final IDirectedGraph<?> node) {
		this(node, new HashMap<IElement, VisualizationWrapperNode>());
	}

	private VisualizationNode(final IDirectedGraph<?> node,
			final HashMap<IElement, VisualizationWrapperNode> backingDirectory) {
		if (backingDirectory.containsKey(node)) {
			mBacking = backingDirectory.get(node);
		} else {

			mBacking = new VisualizationWrapperNode(node) {

				@SuppressWarnings({ "unchecked", "rawtypes" })
				@Override
				protected List<IWalkable> getSuccessors() {
					return (List<IWalkable>) (List) getOutgoingEdges();
				}

				@Override
				protected void createOutgoing() {
					for (IDirectedGraph<?> succ : node.getOutgoingNodes()) {
						mOutgoing.add(new VisualizationEdge(
								VisualizationNode.this, new VisualizationNode(
										succ, backingDirectory), null));
					}
				}

				@Override
				protected void createIncoming() {
					for (IDirectedGraph<?> pred : node.getOutgoingNodes()) {
						mIncoming.add(new VisualizationEdge(
								new VisualizationNode(pred, backingDirectory),
								VisualizationNode.this, null));
					}
				}
			};
			backingDirectory.put(node, mBacking);
		}
	}

	/**
	 * Create a list of successor nodes based on the outgoing edges.
	 * 
	 * @return A list of successor nodes
	 */
	public List<VisualizationNode> getOutgoingNodes() {
		if (mOutgoing == null) {
			mOutgoing = new ArrayList<VisualizationNode>();
			for (VisualizationEdge e : getOutgoingEdges()) {
				mOutgoing.add(e.getTarget());
			}
		}
		return mOutgoing;
	}

	/* --------- IExplicitEdgesMultigraph implementation --------- */

	@Override
	public IPayload getPayload() {
		return mBacking.getPayload();
	}

	@Override
	public boolean hasPayload() {
		return mBacking.hasPayload();
	}

	@Override
	public VisualizationNode getVisualizationGraph() {
		return mBacking.getVisualizationGraph();
	}

	@Override
	public List<IWalkable> getSuccessors() {
		return mBacking.getSuccessors();
	}

	@Override
	public List<VisualizationEdge> getIncomingEdges() {
		return mBacking.getIncomingEdges();
	}

	@Override
	public List<VisualizationEdge> getOutgoingEdges() {
		return mBacking.getOutgoingEdges();
	}

	@Override
	public boolean equals(Object obj) {
		if (obj instanceof VisualizationNode) {
			return mBacking.equals(((VisualizationNode) obj).mBacking);
		}
		return super.equals(obj);
	}

	@Override
	public int hashCode() {
		return mBacking.hashCode();
	}

	@Override
	public String toString() {
		String s = mBacking.toString();
		if (s.length() > 30) {
			s = s.substring(0, 30);
		}
		return s;
	}

	/* ------------------- WrapperNode ------------------ */

	private abstract class VisualizationWrapperNode {

		private final IElement mBackingNode;

		protected List<VisualizationEdge> mOutgoing;
		protected List<VisualizationEdge> mIncoming;

		protected VisualizationWrapperNode(IElement backing) {
			mBackingNode = backing;
		}

		protected IPayload getPayload() {
			return mBackingNode.getPayload();
		}

		protected boolean hasPayload() {
			return mBackingNode.hasPayload();
		}

		protected VisualizationNode getVisualizationGraph() {
			return VisualizationNode.this;
		}

		protected List<VisualizationEdge> getOutgoingEdges() {
			if (mOutgoing == null) {
				mOutgoing = new ArrayList<VisualizationEdge>();
				createOutgoing();
			}
			return mOutgoing;
		}

		protected List<VisualizationEdge> getIncomingEdges() {
			if (mIncoming == null) {
				mIncoming = new ArrayList<VisualizationEdge>();
				createIncoming();
			}
			return mIncoming;
		}

		protected abstract void createIncoming();

		protected abstract void createOutgoing();

		protected abstract List<IWalkable> getSuccessors();

		@Override
		public boolean equals(Object obj) {
			if (obj instanceof VisualizationWrapperNode) {
				return mBackingNode
						.equals(((VisualizationWrapperNode) obj).mBackingNode);
			}
			return super.equals(obj);
		}

		@Override
		public int hashCode() {
			return mBackingNode.hashCode();
		}

		@Override
		public String toString() {
			return mBackingNode.toString();
		}
	}

}
