package de.uni_freiburg.informatik.ultimate.plugins.generator.appgraph;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;

import javax.annotation.PreDestroy;

import de.uni_freiburg.informatik.ultimate.model.annotation.IAnnotations;
import de.uni_freiburg.informatik.ultimate.model.structure.ModifiableExplicitEdgesMultigraph;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck.CodeChecker;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;


/**
 * A ProgramPoint with a predicate. Also includes information about hyperedges.
 *
 * @author Alexander Nutz
 * @author Mohamed Sherif
 * @author Mostafa Mahmoud
 */
public class AnnotatedProgramPoint extends ModifiableExplicitEdgesMultigraph<AnnotatedProgramPoint, AppEdge> {

	private static final long serialVersionUID = -4398335480646555023L;
	
	private IPredicate _predicate;
	private ProgramPoint _programPoint;
	
	private HashSet<AppHyperEdge> _outgoingHyperEdges = new HashSet<AppHyperEdge>();
	
	/**
	 * Constructor of a new AnnotatedProgramPoint.
	 * @param predicate the annotation of the Node
	 * @param programPoint the program point this APP represents
	 * @param isPEL specifies whether or not this APP is considered to be an error location 
	 */
	public AnnotatedProgramPoint(IPredicate predicate, ProgramPoint programPoint) {
		_predicate = predicate;
		_programPoint = programPoint;
	}

	/**
	 * Constructor that copies an old APP to a new one with the same programPoint, predicate, and isPseudoErrorLocation.
	 * @param oldApp the old APP that will be copied
	 */
	public AnnotatedProgramPoint(AnnotatedProgramPoint oldApp) {
		this(oldApp._predicate, oldApp._programPoint);
	}
	
	/**
	 * Constructor that copies an old APP and gives the copy a new predicate.
	 * @param oldApp the old APP that will be copied
	 * @param newPred the predicate of the new copy
	 */
	public AnnotatedProgramPoint(AnnotatedProgramPoint oldApp, IPredicate newPred) {
		this(newPred, oldApp._programPoint);
	}

	/**
	 * Constructor that copies an old APP, copies its outgoing edges if specified to do so, and gives the copy a new predicate.
	 * @param oldApp the old APP that will be copied
	 * @param newPred the predicate of the new copy
	 * @param copyOutgoingEdges if true, the hyperedges will be copied
	 */
	public AnnotatedProgramPoint(AnnotatedProgramPoint oldApp, IPredicate newPred, boolean copyOutgoingEdges) {
		this(oldApp, newPred);
		if(copyOutgoingEdges) {
			for (AppEdge oldOutEdge : oldApp.getOutgoingEdges()) {
				if (oldOutEdge instanceof AppHyperEdge) {
					this.connectOutgoingReturn( 
							((AppHyperEdge) oldOutEdge).getHier(), 
							(Return) oldOutEdge.getStatement(), oldOutEdge.getTarget());
				} else {
					this.connectOutgoing(oldOutEdge.getStatement(), oldOutEdge.getTarget());
				}
			}
			
			for (AppHyperEdge oldOutHypEdge : oldApp.getOutgoingHyperEdges()) {
				oldOutHypEdge.getSource().connectOutgoingReturn(this, (Return) oldOutHypEdge.getStatement(), oldOutHypEdge.getTarget());
			}
		}
	}


	public IPredicate getPredicate() {
		return _predicate;
	}
	
	public boolean isErrorLocation() {
		return _programPoint.isErrorLocation();
	}
	
	public ProgramPoint getProgramPoint() {
		return _programPoint;
	}
	
	public HashSet<AppHyperEdge> getOutgoingHyperEdges() {
		return _outgoingHyperEdges;
	}

//	private boolean noParallelReturns() {
//		boolean result = true;
//		for (int i = 0; i < this.getOutgoingNodes().size(); i++)
//			for (int j = 0; j < this.getOutgoingNodes().size(); j++) //j<i would work too, right?..
//				if (i != j)
//					result &= this.getOutgoingNodes().get(i) != this.getOutgoingNodes().get(j) ||
//						this.getOutgoingEdgeLabels().get(i) != this.getOutgoingEdgeLabels().get(j)	|| 
//						this.getOutgoingReturnCallPreds().get(i) != this.getOutgoingReturnCallPreds().get(j);
//		return result;
//	}

//	/*
//	 * only under this condition we are really allowed to eliminate this node from the set in the ReturnCallPred (hier)
//	 */
//	private boolean noOtherReturnEdgeWithTheSameReturnCallPred(int indexOut) {
//		boolean result = true;
//		for (int i = 0; i < this.getOutgoingNodes().size(); i++)
//			if (i != indexOut)
//				result &= this.getOutgoingReturnCallPreds().get(i).equals(this.getOutgoingReturnCallPreds().get(indexOut));
//		return result;
//	}
	
	public String toString() {
		String ref = CodeChecker.objectReference(this);
		return _programPoint.toString() + 
				ref.substring(Math.max(ref.length() - 3, 0)) + ":" + _predicate.getFormula().toString();
	}
	
	
	public void connectOutgoing(CodeBlock statement, AnnotatedProgramPoint target) {
		assert !(statement instanceof Return);
		AppEdge edge = new AppEdge(this, statement, target);
		this.mOutgoingEdges.add(edge);
		target.mIncomingEdges.add(edge);
	}
	
	public void connectOutgoingReturn(AnnotatedProgramPoint hier, 
			Return returnStm, AnnotatedProgramPoint target) {
		AppHyperEdge hyperEdge = new AppHyperEdge(this, hier, returnStm, target);
		hier._outgoingHyperEdges.add(hyperEdge);
		this.mOutgoingEdges.add(hyperEdge);
		target.mIncomingEdges.add(hyperEdge);
	}
	
	public AppEdge getEdge(AnnotatedProgramPoint target) {
		for (AppEdge edge : mOutgoingEdges) {
			if (edge.getTarget() == target) {
				return edge;
			}
		}
		return null;
	}
	
//	public void disconnectOutgoing(AppEdge outEdge) {
//		if (outEdge instanceof AppHyperEdge) {
//			((AppHyperEdge) outEdge).hier._outgoingHyperEdges.remove(outEdge);
//		}
//	    outEdge.getTarget().mIncomingEdges.remove(outEdge);//TODO: maybe make them HashSets??
//	    this.mOutgoingEdges.remove(outEdge);
//	}
	
	//formerly removed now there again.. --> impulse-specific stuff
	
	private ArrayList<AnnotatedProgramPoint> copies = new ArrayList<AnnotatedProgramPoint>();
	private ArrayList<AnnotatedProgramPoint> newCopies = new ArrayList<AnnotatedProgramPoint>();
	private AnnotatedProgramPoint cloneSource;

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
}
