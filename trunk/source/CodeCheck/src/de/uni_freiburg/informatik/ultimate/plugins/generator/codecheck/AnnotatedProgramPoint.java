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
	 * copy constructor
	 * @param oldApp AnnotatedProgramPoint to copy
	 */
	
	
	
	/**
	 * copy constructor, except for a new predicate, which is given as an argument
	 * @param oldApp AnnotatedProgramPoint to copy
	 * @param newPred
	 */
	
	@SuppressWarnings("unchecked")
	private HashMap <AnnotatedProgramPoint, HashSet<AnnotatedProgramPoint>> cloneMap(HashMap <AnnotatedProgramPoint, HashSet<AnnotatedProgramPoint>> map) {
		HashMap <AnnotatedProgramPoint, HashSet<AnnotatedProgramPoint>> ret = new HashMap<AnnotatedProgramPoint, HashSet<AnnotatedProgramPoint>>();
		for (AnnotatedProgramPoint key : map.keySet()) {
			ret.put(key, (HashSet<AnnotatedProgramPoint>) map.get(key).clone());
		}
		return ret;
	}
	
	
	
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
	
	public AnnotatedProgramPoint(IPredicate predicate, ProgramPoint programPoint) {
		this(predicate, programPoint, false);
	}
	
	public AnnotatedProgramPoint(AnnotatedProgramPoint oldApp, IPredicate newPred) {
		this(newPred, oldApp.m_programPoint, oldApp.m_isPseudoErrorLocation);
	}
	
	public AnnotatedProgramPoint(AnnotatedProgramPoint oldApp) {
		this(oldApp.m_predicate, oldApp.m_programPoint, oldApp.m_isPseudoErrorLocation);
	}

	public AnnotatedProgramPoint(AnnotatedProgramPoint oldApp, IPredicate newPred, boolean copyReturnAppToCallPredsLists) {
		this(newPred, oldApp.m_programPoint, oldApp.m_isPseudoErrorLocation);
		if(copyReturnAppToCallPredsLists) {
			m_outgoingReturnAppToCallPreds = cloneMap(oldApp.m_outgoingReturnAppToCallPreds);
			m_ingoingReturnAppToCallPreds = cloneMap(oldApp.m_ingoingReturnAppToCallPreds);
		}
	}

	public void addCopy(AnnotatedProgramPoint copy) {
		newCopies.add(copy);
	}
	
	public void updateCopies() {
		copies.addAll(newCopies);
		newCopies.clear();
	}
	
	public void setCloneSource(AnnotatedProgramPoint source) {
		cloneSource = source;
	}
	
	public ArrayList<AnnotatedProgramPoint> getCopies() {
		ArrayList<AnnotatedProgramPoint> result = new ArrayList<AnnotatedProgramPoint>();
		result.addAll(copies);
		result.addAll(newCopies);
		return result;
	}
	
	public ArrayList<AnnotatedProgramPoint> getNewCopies() {
		return newCopies;
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
			if (callPred.m_ingoingReturnAppToCallPreds.get(this) != null && callPred.m_ingoingReturnAppToCallPreds.get(this).isEmpty()) {
				callPred.m_ingoingReturnAppToCallPreds.remove(this);
			}
			return true;
		}
		else
			return false;
	}
	
	public boolean outGoingReturnAppToCallPredContains(AnnotatedProgramPoint target, AnnotatedProgramPoint callPred) {
		if (!( this.mOutgoingEdgeLabels.get(target) instanceof Return))
			return false;
		assert m_outgoingReturnAppToCallPreds != null; 
		
		if (m_outgoingReturnAppToCallPreds.get(target) == null)
			return false;
		
		return m_outgoingReturnAppToCallPreds.get(target).contains(callPred);
	}
	
	public HashSet<AnnotatedProgramPoint> getCallPredsOfOutgoingReturnTarget(AnnotatedProgramPoint returnTarget) {
		assert m_outgoingReturnAppToCallPreds != null;
		return m_outgoingReturnAppToCallPreds.get(returnTarget);
	}

	public void connectTo(AnnotatedProgramPoint dest, CodeBlock label) {
		addOutgoingNode(dest, label);
		dest.addIncomingNode(this);
	}
	public void disconnectFrom(AnnotatedProgramPoint dest) {
		if(this.getOutgoingEdgeLabel(dest) instanceof Return)
			this.m_outgoingReturnAppToCallPreds.remove(dest);
		this.removeOutgoingNode(dest);
		dest.removeIncomingNode(this);
	}
	
	public IPayload getPayload() {
		return m_programPoint.getPayload();
	}
	
	public String toString() {
		return m_programPoint.toString(); //+ ":" + m_predicate.toString();
	}

	public void setIsPseudoErrorLocation(boolean value) {
		m_isPseudoErrorLocation = value;
	}
	
	public boolean isPseudoErrorLocation() {
		return m_isPseudoErrorLocation;
	}
}
