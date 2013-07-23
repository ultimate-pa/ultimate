package de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;

import de.uni_freiburg.informatik.ultimate.model.IPayload;
import de.uni_freiburg.informatik.ultimate.model.structure.ModifiableLabeledEdgesMultigraph;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.IPredicate;


/**
 * A ProgramPoint with a predicate. Also includes information about hyperedges.
 *
 * @author Alexander Nutz
 * @author Mohamed Sherif
 */
public class AnnotatedProgramPoint extends ModifiableLabeledEdgesMultigraph<AnnotatedProgramPoint, CodeBlock> {

	private static final long serialVersionUID = -4398335480646555023L;
	
	private IPredicate m_predicate;
	private ProgramPoint m_programPoint;
	
	boolean m_isPseudoErrorLocation = false;

	private ArrayList<AnnotatedProgramPoint> copies;
	private ArrayList<AnnotatedProgramPoint> newCopies;
	private AnnotatedProgramPoint cloneSource;
	
	public HashMap<AnnotatedProgramPoint, HashSet<AnnotatedProgramPoint>> m_outgoingReturnAppToCallPreds;
	public HashMap<AnnotatedProgramPoint, HashSet<AnnotatedProgramPoint>> m_ingoingReturnAppToCallPreds;
	
	/**
	 * Constructor of a new AnnotatedProgramPoint.
	 * @param predicate the annotation of the Node
	 * @param programPoint the program point this APP represents
	 * @param isPEL specifies whether or not this APP is considered to be an error location 
	 */
	public AnnotatedProgramPoint(IPredicate predicate, ProgramPoint programPoint, boolean isPEL) {
		m_predicate = predicate;
		m_programPoint = programPoint;
		m_isPseudoErrorLocation = isPEL;
		copies = new ArrayList<AnnotatedProgramPoint>();
		newCopies = new ArrayList<AnnotatedProgramPoint>();
		m_outgoingReturnAppToCallPreds = new HashMap<AnnotatedProgramPoint, HashSet<AnnotatedProgramPoint>>();
		m_ingoingReturnAppToCallPreds = new HashMap<AnnotatedProgramPoint, HashSet<AnnotatedProgramPoint>>();
		cloneSource = null;
	}
	
	/**
	 * Constructor of a new AnnotatedProgramPoint that's not an error location.
	 * @param predicate the annotation of the Node
	 * @param programPoint the program point this APP represents
	 */
	public AnnotatedProgramPoint(IPredicate predicate, ProgramPoint programPoint) {
		this(predicate, programPoint, false);
	}

	/**
	 * Constructor that copies an old APP to a new one with the same programPoint, predicate, and isPseudoErrorLocation.
	 * @param oldApp the old APP that will be copied
	 */
	public AnnotatedProgramPoint(AnnotatedProgramPoint oldApp) {
		this(oldApp.m_predicate, oldApp.m_programPoint, oldApp.m_isPseudoErrorLocation);
	}
	
	/**
	 * Constructor that copies an old APP and gives the copy a new predicate.
	 * @param oldApp the old APP that will be copied
	 * @param newPred the predicate of the new copy
	 */
	public AnnotatedProgramPoint(AnnotatedProgramPoint oldApp, IPredicate newPred) {
		this(newPred, oldApp.m_programPoint, oldApp.m_isPseudoErrorLocation);
	}

	/**
	 * Constructor that copies an old APP, copies its outgoing edges if specified to do so, and gives the copy a new predicate.
	 * @param oldApp the old APP that will be copied
	 * @param newPred the predicate of the new copy
	 * @param copyOutgoingEdges if true, the hyperedges will be copied
	 */
	public AnnotatedProgramPoint(AnnotatedProgramPoint oldApp, IPredicate newPred, boolean copyOutgoingEdges) {
		this(newPred, oldApp.m_programPoint, oldApp.m_isPseudoErrorLocation);
		if(copyOutgoingEdges) {
			for(AnnotatedProgramPoint dest : oldApp.getOutgoingNodes()) {
				this.connectTo(dest, oldApp.getOutgoingEdgeLabel(dest));
			}
			AnnotatedProgramPoint[] targets = oldApp.m_outgoingReturnAppToCallPreds.keySet().toArray(new AnnotatedProgramPoint[]{});
			for (AnnotatedProgramPoint target : targets) {
				AnnotatedProgramPoint[] callPreds = oldApp.m_outgoingReturnAppToCallPreds.get(target).toArray(new AnnotatedProgramPoint[]{});
				for (AnnotatedProgramPoint callPred : callPreds) {
					addOutGoingReturnCallPred(target, callPred);
				}
			}
			AnnotatedProgramPoint[] sources = oldApp.m_ingoingReturnAppToCallPreds.keySet().toArray(new AnnotatedProgramPoint[]{});
			for (AnnotatedProgramPoint source : sources) {
				targets = oldApp.m_ingoingReturnAppToCallPreds.get(source).toArray(new AnnotatedProgramPoint[]{});
				for (AnnotatedProgramPoint target : targets) {
					source.addOutGoingReturnCallPred(target, this);
				}
			}
		}
	}

	/**
	 * Adds an APP to the list of new copies of this APP.
	 * @param copy the APP that will be added as a copy to this APP
	 */
	public void addCopy(AnnotatedProgramPoint copy) {
		newCopies.add(copy);
	}

	/**
	 * Moves new copies to the list of old copies.
	 */
	public void updateCopies() {
		copies.addAll(newCopies);
		newCopies.clear();
	}

	/**
	 * Sets the clone source of this APP. The clone source is the APP copies to form this APP.
	 * @param source the APP that should be declared to be the clone source
	 */
	public void setCloneSource(AnnotatedProgramPoint source) {
		cloneSource = source;
	}

	/**
	 * Gets a list of all the copies of this APP.
	 * @return returns a list of copies of this APP
	 */
	public ArrayList<AnnotatedProgramPoint> getCopies() {
		ArrayList<AnnotatedProgramPoint> ret = new ArrayList<AnnotatedProgramPoint>();
		ret.addAll(copies);
		ret.addAll(newCopies);
		return ret;
	}

	/**
	 * Gets a clone of the list of new copies of this APP.
	 * @return returns a list of new copies of this APP
	 */
	public ArrayList<AnnotatedProgramPoint> getNewCopies() {
		ArrayList<AnnotatedProgramPoint> ret = new ArrayList<AnnotatedProgramPoint>();
		ret.addAll(newCopies);
		return ret;
	}
	
	public IPredicate getPredicate() {
		return m_predicate;
	}
	
	public void setPredicate(IPredicate predicate) {
		m_predicate = predicate;
	}
	
	public boolean isErrorLocation() {
		return m_programPoint.isErrorLocation();
	}
	
	public ProgramPoint getProgramPoint() {
		return m_programPoint;
	}


	/**
	 * Adds a hyper edge having this APP as a direct source.
	 * @param target the destination of the hyper edge
	 * @param callPred the call predecessor of the hyper edge
	 * @return returns true if addition of the hyper edge was successful, false if the hyper edge already existed
	 */
	public boolean addOutGoingReturnCallPred(AnnotatedProgramPoint target, AnnotatedProgramPoint callPred) {
		assert mOutgoingEdgeLabels.get(target) instanceof Return;
		
		if (m_outgoingReturnAppToCallPreds == null) {
			m_outgoingReturnAppToCallPreds = new HashMap<AnnotatedProgramPoint, HashSet<AnnotatedProgramPoint>>();
		}
		
		HashSet <AnnotatedProgramPoint> hyperEdges = m_outgoingReturnAppToCallPreds.get(target);
		if (hyperEdges == null) {
			hyperEdges = new HashSet<AnnotatedProgramPoint>();
			m_outgoingReturnAppToCallPreds.put(target, hyperEdges);
		}
		
		boolean added = hyperEdges.add(callPred);
		
		if (callPred.m_ingoingReturnAppToCallPreds == null) {
			callPred.m_ingoingReturnAppToCallPreds = new HashMap<AnnotatedProgramPoint, HashSet<AnnotatedProgramPoint>>();
		}
		HashSet <AnnotatedProgramPoint> returns = callPred.m_ingoingReturnAppToCallPreds.get(this);
		if (returns == null) {
			returns = new HashSet<AnnotatedProgramPoint>();
			callPred.m_ingoingReturnAppToCallPreds.put(this, returns);
		}
		returns.add(target);
		
		return added;
	}

	/**
	 * Removes a hyper edge which has this APP as a direct source.
	 * @param target the destination of the hyper edge
	 * @param callPred the call predecessor of the hyper edge
	 * @return returns true if removing the hyper edge was successful, false if the hyper edge didn't even exist
	 */
	public boolean removeOutgoingReturnCallPred(AnnotatedProgramPoint target, AnnotatedProgramPoint callPred) {
		assert mOutgoingEdgeLabels.get(target) instanceof Return;
		assert m_outgoingReturnAppToCallPreds != null && m_outgoingReturnAppToCallPreds.get(target) != null;
		assert callPred.m_ingoingReturnAppToCallPreds != null && callPred.m_ingoingReturnAppToCallPreds.get(this) != null;
	
		
		if(m_outgoingReturnAppToCallPreds == null)
			return false;
		if(m_outgoingReturnAppToCallPreds.get(target) == null)
			return false;
		
		if (m_outgoingReturnAppToCallPreds.get(target).contains(callPred)) {
			m_outgoingReturnAppToCallPreds.get(target).remove(callPred);
			callPred.m_ingoingReturnAppToCallPreds.get(this).remove(target);
			
			if (m_outgoingReturnAppToCallPreds.get(target).isEmpty()) {
				m_outgoingReturnAppToCallPreds.remove(target);
			}
			if (callPred.m_ingoingReturnAppToCallPreds.get(this).isEmpty()) {
				callPred.m_ingoingReturnAppToCallPreds.remove(this);
			}
			return true;
		}
		else
			return false;
	}

	/**
	 * Checks whether a hyper edges exists or not. The direct source of the hyper edge is this APP
	 * @param target the destination of the hyper edge
	 * @param callPred the call predecessor of the hyper edge
	 * @return returns true if the hyper edge was found, false otherwise
	 */
	public boolean outGoingReturnAppToCallPredContains(AnnotatedProgramPoint target, AnnotatedProgramPoint callPred) {
		if (!( this.mOutgoingEdgeLabels.get(target) instanceof Return))
			return false;
		assert m_outgoingReturnAppToCallPreds != null; 
		
		if (m_outgoingReturnAppToCallPreds.get(target) == null)
			return false;
		
		return m_outgoingReturnAppToCallPreds.get(target).contains(callPred);
	}

	/**
	 * Gets the list of hyper edges from this APP to a specified destination.
	 * Each element of the returned list represents a hyper edge having that element as a call predecessor, this node as a direct source, and returnTarget as a destination
	 * @param returnTarget the destination of the hyper edge
	 * @return returns a list of call predecessors
	 */
	public HashSet<AnnotatedProgramPoint> getCallPredsOfOutgoingReturnTarget(AnnotatedProgramPoint returnTarget) {
		assert m_outgoingReturnAppToCallPreds != null;
		return m_outgoingReturnAppToCallPreds.get(returnTarget); //.clone();
	}

	/**
	 * Connects this APP to the specified target with an edge of the specified label
	 * @param dest the destination of the edge
	 * @param label the label of the edge
	 */
	public void connectTo(AnnotatedProgramPoint dest, CodeBlock label) {
		if(this.getOutgoingNodes().contains(dest))
			return;
		addOutgoingNode(dest, label);
		dest.addIncomingNode(this);
	}

	/**
	 * Disconnects this APP from the specified target. If there exists hyperedges between the 2 APP, they will be removed as well.
	 * @param dest the destination that will be disconnected from this APP
	 */
	public void disconnectFrom(AnnotatedProgramPoint dest) {
		if(!this.getOutgoingNodes().contains(dest))
			return;
		if(this.getOutgoingEdgeLabel(dest) instanceof Return) {
			AnnotatedProgramPoint[] callPreds = this.m_outgoingReturnAppToCallPreds.get(dest).toArray(new AnnotatedProgramPoint[]{});
			for (AnnotatedProgramPoint callPred : callPreds) {
				removeOutgoingReturnCallPred(dest, callPred);
			}
		}
		this.removeOutgoingNode(dest);
		dest.removeIncomingNode(this);
	}
	
	public IPayload getPayload() {
		return m_programPoint.getPayload();
	}
	
	public String toString() {
		return m_programPoint.toString() + CodeChecker.objectReference(this);// + ":" + m_predicate.toString();
	}

	public void setIsPseudoErrorLocation(boolean value) {
		m_isPseudoErrorLocation = value;
	}
	
	public boolean isPseudoErrorLocation() {
		return m_isPseudoErrorLocation;
	}
}
