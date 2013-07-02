package de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.model.IPayload;
import de.uni_freiburg.informatik.ultimate.model.structure.BaseLabeledEdgesMultigraph;
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
	
	private HashMap<AnnotatedProgramPoint, HashSet<AnnotatedProgramPoint>> m_outgoingReturnAppToCallPreds;
	
	/**
	 * copy constructor
	 * @param oldApp AnnotatedProgramPoint to copy
	 */
	public AnnotatedProgramPoint(AnnotatedProgramPoint oldApp) {
		m_predicate = oldApp.m_predicate;
		m_programPoint = oldApp.m_programPoint;
		m_isPseudoErrorLocation = oldApp.m_isPseudoErrorLocation;
		m_outgoingReturnAppToCallPreds = oldApp.m_outgoingReturnAppToCallPreds;
		copies = new ArrayList<AnnotatedProgramPoint>();
		newCopies = new ArrayList<AnnotatedProgramPoint>();
		cloneSource = null;
	}
	
	
	/**
	 * copy constructor, except for a new predicate, which is given as an argument
	 * @param oldApp AnnotatedProgramPoint to copy
	 * @param newPred
	 */
	public AnnotatedProgramPoint(AnnotatedProgramPoint oldApp, IPredicate newPred) {
		m_predicate = newPred;
		m_programPoint = oldApp.m_programPoint;
		m_isPseudoErrorLocation = oldApp.m_isPseudoErrorLocation;
		m_outgoingReturnAppToCallPreds = oldApp.m_outgoingReturnAppToCallPreds;
		copies = new ArrayList<AnnotatedProgramPoint>();
		newCopies = new ArrayList<AnnotatedProgramPoint>();
		cloneSource = null;
	}
	
	public AnnotatedProgramPoint(IPredicate predicate, ProgramPoint programPoint) {
		m_predicate = predicate;
		m_programPoint = programPoint;
		copies = new ArrayList<AnnotatedProgramPoint>();
		newCopies = new ArrayList<AnnotatedProgramPoint>();
		m_outgoingReturnAppToCallPreds = new HashMap<AnnotatedProgramPoint, HashSet<AnnotatedProgramPoint>>();
		cloneSource = null;
	}
	
	public AnnotatedProgramPoint(IPredicate predicate, ProgramPoint programPoint, boolean isPEL) {
		m_predicate = predicate;
		m_programPoint = programPoint;
		m_isPseudoErrorLocation = isPEL;
		copies = new ArrayList<AnnotatedProgramPoint>();
		newCopies = new ArrayList<AnnotatedProgramPoint>();
		m_outgoingReturnAppToCallPreds = new HashMap<AnnotatedProgramPoint, HashSet<AnnotatedProgramPoint>>();
		cloneSource = null;
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
	
	public void addOutGoingReturnCallPred(AnnotatedProgramPoint target, AnnotatedProgramPoint callPred) {
		assert mOutgoingEdgeLabels.get(target) instanceof Return;
		
		if (m_outgoingReturnAppToCallPreds == null)
			m_outgoingReturnAppToCallPreds = new HashMap<AnnotatedProgramPoint, HashSet<AnnotatedProgramPoint>>();
		
		if (m_outgoingReturnAppToCallPreds.get(target) == null)
			m_outgoingReturnAppToCallPreds.put(target, new HashSet<AnnotatedProgramPoint>());
		
		m_outgoingReturnAppToCallPreds.get(target).add(callPred);
	}
	
	public void removeOutgoingReturnCallPred(AnnotatedProgramPoint target, AnnotatedProgramPoint callPred) {
		assert mOutgoingEdgeLabels.get(target) instanceof Return;
		assert m_outgoingReturnAppToCallPreds != null && m_outgoingReturnAppToCallPreds.get(target) != null;
		
		m_outgoingReturnAppToCallPreds.get(target).remove(callPred);		
	}
	
	public boolean outGoingReturnAppToCallPredContains(AnnotatedProgramPoint target, AnnotatedProgramPoint callPred) {
		if (!( mOutgoingEdgeLabels.get(target) instanceof Return))
			return false;
		assert m_outgoingReturnAppToCallPreds != null; 
		
		if (m_outgoingReturnAppToCallPreds.get(target) == null)
			return false;
		
		return m_outgoingReturnAppToCallPreds.get(target).contains(callPred);
	}
	
	public HashSet<AnnotatedProgramPoint> getCallPredsOfOutgoingReturnTarget(AnnotatedProgramPoint returnTarget) {
		if (m_outgoingReturnAppToCallPreds == null)
			System.err.println("WHAHAAA!");
		return m_outgoingReturnAppToCallPreds.get(returnTarget);
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
