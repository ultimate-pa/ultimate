package de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck;

import java.util.ArrayList;
import java.util.HashSet;

import de.uni_freiburg.informatik.ultimate.model.IPayload;
import de.uni_freiburg.informatik.ultimate.model.structure.ModifiableExplicitEdgesMultigraph;
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
//	public AnnotatedProgramPoint(AnnotatedProgramPoint oldApp, IPredicate newPred, boolean copyOutgoingEdges) {
//		this(newPred, oldApp._programPoint);
//		if(copyOutgoingEdges) {
//			for (int i = 0; i < oldApp.getOutgoingNodes().size(); i++) {
//				CodeBlock edgeLabel = oldApp.getOutgoingEdgeLabels().get(i);
//				if (edgeLabel instanceof Return)
//					this.connectOutgoingWithReturn(oldApp.getOutgoingNodes().get(i), 
//							(Return) edgeLabel, 
//							oldApp.getOutgoingReturnCallPreds().get(i));
//				else
//					this.connectOutgoing(oldApp.getOutgoingNodes().get(i), edgeLabel);
//			}
//		}
//	}


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
		return _programPoint.toString() + 
				CodeChecker.objectReference(this);// + ":" + m_predicate.toString();
	}
	
	
	public void connectOutgoing(AnnotatedProgramPoint target, CodeBlock statement) {
		assert !(statement instanceof Return);
		AppEdge edge = new AppEdge(this, statement, target);
		this.mOutgoingEdges.add(edge);
		target.mIncomingEdges.add(edge);
	}
	
	public void connectOutgoingReturn(AnnotatedProgramPoint target, AnnotatedProgramPoint hier, 
			Return returnStm) {
		AppHyperEdge hyperEdge = new AppHyperEdge(this, hier, returnStm, target);
		hier._outgoingHyperEdges.add(hyperEdge);
		this.mOutgoingEdges.add(hyperEdge);
		target.mIncomingEdges.add(hyperEdge);
	}
	
//	public void disconnectOutgoing(AppEdge outEdge) {
//		if (outEdge instanceof AppHyperEdge) {
//			((AppHyperEdge) outEdge).hier._outgoingHyperEdges.remove(outEdge);
//		}
//	    outEdge.getTarget().mIncomingEdges.remove(outEdge);//TODO: maybe make them HashSets??
//	    this.mOutgoingEdges.remove(outEdge);
//	}
}
