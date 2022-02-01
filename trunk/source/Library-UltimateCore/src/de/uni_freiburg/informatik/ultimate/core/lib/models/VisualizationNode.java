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

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.core.model.IOutput;
import de.uni_freiburg.informatik.ultimate.core.model.models.IDirectedGraph;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.models.IExplicitEdgesMultigraph;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILabeledEdgesMultigraph;
import de.uni_freiburg.informatik.ultimate.core.model.models.IMultigraphEdge;
import de.uni_freiburg.informatik.ultimate.core.model.models.IPayload;
import de.uni_freiburg.informatik.ultimate.core.model.models.ISimpleAST;
import de.uni_freiburg.informatik.ultimate.core.model.models.IVisualizable;
import de.uni_freiburg.informatik.ultimate.core.model.models.IWalkable;

/***
 * VisualizationNode is the Ultimate model for graph visualizations. It wraps every other graph structure and provides a
 * unified interface for {@link IOutput} plugins through the {@link IVisualizable} interface.
 * 
 * In general, each {@link IVisualizable} type has a corresponding constructor in this class that creates a anonymous
 * sub-class of the inner class WrapperNode which builds a visualization structure through lazy initialization. This
 * visualization structure corresponds to a directed multigraph described through {@link IExplicitEdgesMultigraph}. The
 * corresponding edge type is {@link VisualizationEdge}.
 * 
 * Please note that the resulting visualization structure can be larger than the original graph structure, as cycles may
 * lead to multiple WrapperNodes for a single original node (same for edges).
 * 
 * {@link IOutput} implementations have to ensure that they always use the {@link VisualizationNode#equals(Object)} and
 * {@link VisualizationEdge} {@link #equals(Object)} methods to compare instances of those structures, as they will
 * return true if the backing is the same for two different instances.
 * 
 * @author dietsch
 * @see VisualizationEdge
 * @see IExplicitEdgesMultigraph
 */
public final class VisualizationNode implements
		IExplicitEdgesMultigraph<VisualizationNode, VisualizationEdge, VisualizationNode, VisualizationEdge, VisualizationNode> {
	
	private static final long serialVersionUID = 1L;
	
	private final VisualizationWrapperNode mBacking;
	private List<VisualizationNode> mOutgoing;
	
	public VisualizationNode(final IExplicitEdgesMultigraph<?, ?, ?, ?, VisualizationNode> node) {
		mBacking = new VisualizationWrapperNode(node) {
			
			@Override
			protected void createIncoming() {
				for (final IMultigraphEdge<?, ?, ?, ?, VisualizationNode> e : node.getIncomingEdges()) {
					if (e.getSource() != null) {
						VisualizationEdge ve;
						if (e.hasPayload()) {
							ve = new VisualizationEdge(e.getSource().getVisualizationGraph(), VisualizationNode.this,
									e.getPayload(), e);
						} else {
							ve = new VisualizationEdge(e.getSource().getVisualizationGraph(), VisualizationNode.this,
									e);
						}
						mIncoming.add(ve);
					}
				}
			}
			
			@Override
			protected void createOutgoing() {
				for (final IMultigraphEdge<?, ?, ?, ?, VisualizationNode> e : node.getOutgoingEdges()) {
					if (e.getTarget() != null) {
						VisualizationEdge ve;
						if (e.hasPayload()) {
							ve = new VisualizationEdge(VisualizationNode.this, e.getTarget().getVisualizationGraph(),
									e.getPayload(), e);
						} else {
							ve = new VisualizationEdge(VisualizationNode.this, e.getTarget().getVisualizationGraph(),
									e);
						}
						mOutgoing.add(ve);
					}
				}
				
			}
			
			@SuppressWarnings({ "unchecked", "rawtypes" })
			@Override
			protected List<IWalkable> getSuccessors() {
				return (List) getOutgoingEdges();
			}
		};
		
	}
	
	private static IPayload extractPayload(final Object label) {
		IPayload pay = null;
		if (label instanceof IPayload) {
			pay = (IPayload) label;
		} else if (label instanceof IElement) {
			final IElement ele = (IElement) label;
			if (ele.hasPayload()) {
				pay = ele.getPayload();
			}
		}
		return pay;
	}
	
	public <T extends ILabeledEdgesMultigraph<T, L, VisualizationNode>, L> VisualizationNode(
			final ILabeledEdgesMultigraph<T, L, VisualizationNode> node) {
		// TODO: We need to handle the case where L is an instance of an
		// collection (i.e. multigraph)
		mBacking = new VisualizationWrapperNode(node) {
			
			@SuppressWarnings("unchecked")
			@Override
			protected void createIncoming() {
				for (final ILabeledEdgesMultigraph<T, L, VisualizationNode> pred : node.getIncomingNodes()) {
					VisualizationEdge ve;
					final IPayload pay = extractPayload(node.getIncomingEdgeLabel((T) pred));
					
					if (pay != null) {
						ve = new VisualizationEdge(pred.getVisualizationGraph(), VisualizationNode.this, pay, null);
					} else {
						ve = new VisualizationEdge(pred.getVisualizationGraph(), VisualizationNode.this, null);
					}
					mIncoming.add(ve);
				}
				
			}
			
			@SuppressWarnings("unchecked")
			@Override
			protected void createOutgoing() {
				for (final ILabeledEdgesMultigraph<T, L, VisualizationNode> succ : node.getOutgoingNodes()) {
					VisualizationEdge ve;
					final IPayload pay = extractPayload(node.getOutgoingEdgeLabel((T) succ));
					
					if (pay != null) {
						ve = new VisualizationEdge(VisualizationNode.this, succ.getVisualizationGraph(), pay, null);
					} else {
						ve = new VisualizationEdge(
								
								VisualizationNode.this, succ.getVisualizationGraph(), null);
					}
					mOutgoing.add(ve);
				}
				
			}
			
			@Override
			protected List<IWalkable> getSuccessors() {
				final ArrayList<IWalkable> rtr = new ArrayList<>();
				for (final ILabeledEdgesMultigraph<T, L, VisualizationNode> succ : node.getOutgoingNodes()) {
					final ILabeledEdgesMultigraph<T, L, VisualizationNode> child = succ;
					rtr.add(new IWalkableImplementation(node, child));
				}
				return rtr;
			}
		};
	}
	
	public VisualizationNode(final ISimpleAST<?, VisualizationNode> node) {
		mBacking = new VisualizationWrapperNode(node) {
			
			@SuppressWarnings({ "unchecked", "rawtypes" })
			@Override
			protected List<IWalkable> getSuccessors() {
				return (List) getOutgoingEdges();
			}
			
			@Override
			protected void createOutgoing() {
				// we also create the incoming edge for this tree if we traverse
				// in the right order
				mIncoming = new ArrayList<>();
				
				for (final ISimpleAST<?, VisualizationNode> succ : node.getOutgoingNodes()) {
					if (succ == null) {
						continue;
					}
					VisualizationEdge ve;
					if (succ.hasPayload()) {
						ve = new VisualizationEdge(VisualizationNode.this, succ.getVisualizationGraph(),
								succ.getPayload(), succ);
					} else {
						ve = new VisualizationEdge(VisualizationNode.this, succ.getVisualizationGraph(), succ);
					}
					mOutgoing.add(ve);
				}
			}
			
			@Override
			protected void createIncoming() {
				// we only warn here, because after a call to getOutgoingEdges
				// the incomingEdges should be initialized
			}
		};
	}
	
	public VisualizationNode(final IDirectedGraph<?, VisualizationNode> node) {
		this(node, new HashMap<IElement, VisualizationWrapperNode>());
	}
	
	private VisualizationNode(final IDirectedGraph<?, VisualizationNode> node,
			final HashMap<IElement, VisualizationWrapperNode> backingDirectory) {
		if (backingDirectory.containsKey(node)) {
			mBacking = backingDirectory.get(node);
		} else {
			
			mBacking = new VisualizationWrapperNode(node) {
				
				@SuppressWarnings({ "unchecked", "rawtypes" })
				@Override
				protected List<IWalkable> getSuccessors() {
					return (List) getOutgoingEdges();
				}
				
				@Override
				protected void createOutgoing() {
					for (final IDirectedGraph<?, VisualizationNode> succ : node.getOutgoingNodes()) {
						mOutgoing.add(new VisualizationEdge(VisualizationNode.this,
								new VisualizationNode(succ, backingDirectory), null));
					}
				}
				
				@Override
				protected void createIncoming() {
					for (final IDirectedGraph<?, VisualizationNode> pred : node.getOutgoingNodes()) {
						mIncoming.add(new VisualizationEdge(new VisualizationNode(pred, backingDirectory),
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
			mOutgoing = new ArrayList<>();
			for (final VisualizationEdge e : getOutgoingEdges()) {
				mOutgoing.add(e.getTarget());
			}
		}
		return mOutgoing;
	}
	
	public Object getBacking() {
		if (mBacking == null) {
			return null;
		}
		return mBacking.mBackingNode;
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
	public boolean equals(final Object obj) {
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
	
	@Override
	public VisualizationNode getLabel() {
		return this;
	}
	
	/* ------------------- WrapperNode ------------------ */
	
	private final class IWalkableImplementation<T extends ILabeledEdgesMultigraph<T, L, VisualizationNode>, L>
			implements IWalkable {
		private final T mNode;
		private final T mChild;
		private static final long serialVersionUID = 1L;
		
		private IWalkableImplementation(final T node, final T child) {
			mNode = node;
			mChild = child;
		}
		
		@Override
		public boolean hasPayload() {
			return extractPayload(mNode.getOutgoingEdgeLabel(mChild)) != null;
		}
		
		@Override
		public IPayload getPayload() {
			return extractPayload(mNode.getOutgoingEdgeLabel(mChild));
		}
		
		@Override
		public List<IWalkable> getSuccessors() {
			return Collections.singletonList((IWalkable) mChild);
		}
	}
	
	private abstract class VisualizationWrapperNode {
		
		private final IElement mBackingNode;
		
		protected List<VisualizationEdge> mOutgoing;
		protected List<VisualizationEdge> mIncoming;
		
		protected VisualizationWrapperNode(final IElement backing) {
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
				mOutgoing = new ArrayList<>();
				createOutgoing();
			}
			return mOutgoing;
		}
		
		protected List<VisualizationEdge> getIncomingEdges() {
			if (mIncoming == null) {
				mIncoming = new ArrayList<>();
				createIncoming();
			}
			return mIncoming;
		}
		
		protected abstract void createIncoming();
		
		protected abstract void createOutgoing();
		
		protected abstract List<IWalkable> getSuccessors();
		
		@Override
		public boolean equals(final Object obj) {
			if (obj instanceof VisualizationWrapperNode) {
				return mBackingNode.equals(((VisualizationWrapperNode) obj).mBackingNode);
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
