/*
 * Project:	CoreRCP
 * Package:	de.uni_freiburg.informatik.ultimate.model
 * File:	Edge.java created on Nov 18, 2009 by Björn Buchhold
 *
 */
package de.uni_freiburg.informatik.ultimate.model;

import java.util.Collections;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.model.structure.IWalkable;

/**
 * Edge
 * 
 * Default implementation of {@link IEdge} The edges keeps references to the
 * nodes that are its source and target.
 * 
 * Edges can be constructed with, or without a payload (results in the payload
 * being null)
 * 
 * @author Björn Buchhold
 * 
 */
public class Edge extends AbstractElement implements IEdge {

	/**
	 * long serialVersionUID
	 */
	private static final long serialVersionUID = 9219656346077957049L;

	private INode source;
	private INode target;

	/**
	 * Constructs an Edge with between the provided {@link INode}'s, carrying
	 * the {@link IPayload} passed as parameter
	 * 
	 * @param src
	 *            the source Node
	 * @param target
	 *            the target node
	 * @param payload
	 *            the payload
	 */
	public Edge(INode src, INode target, IPayload payload) {
		this.source = src;
		this.target = target;
		this.payload = payload;
	}

	/**
	 * Constructs an Edge with between the provided {@link INode}'s, carrying
	 * null as {@link IPayload}
	 * 
	 * @param src
	 *            the source Node
	 * @param target
	 *            the target Node
	 */
	public Edge(INode src, INode target) {
		this(src, target, null);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.model.IEdge#getSource()
	 */
	@Override
	public INode getSource() {
		return this.source;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.model.IEdge#getTarget()
	 */
	@Override
	public INode getTarget() {
		return this.target;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * de.uni_freiburg.informatik.ultimate.model.IEdge#setSource(de.uni_freiburg
	 * .informatik.ultimate.model.INode)
	 */
	@Override
	public void setSource(INode source) {
		this.source = source;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * de.uni_freiburg.informatik.ultimate.model.IEdge#setTarget(de.uni_freiburg
	 * .informatik.ultimate.model.INode)
	 */
	@Override
	public void setTarget(INode target) {
		this.target = target;
	}

	@Override
	public List<IWalkable> getSuccessors() {
		return Collections.singletonList((IWalkable) target);
	}

}
