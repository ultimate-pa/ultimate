package de.uni_freiburg.informatik.ultimate.modelcheckerutils.errortrace;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.core.coreplugin.Activator;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.model.IEdge;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.model.INode;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Procedure;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ReturnStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.annotations.CFGNodeAnnotations;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.annotations.SCNodeAnnotations;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.annotations.SMTEdgeAnnotations;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.VariableSSAManager;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfgelements.CFGEdge;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfgelements.CFGExplicitNode;

public class ErrorTrace extends IErrorTrace {

	/**
	 * 
	 */
	private static final long serialVersionUID = 2491619769649163147L;
	
	ArrayList<IElement> mErrorPath = null;
	Term[] mFormulas = null;
	Logger logger = UltimateServices.getInstance().getLogger(Activator.s_PLUGIN_ID);

	public ErrorTrace(Script script, ArrayList<IElement> errorPath, Term[] formulas) {
		super(script);
		mErrorPath = errorPath;
		mFormulas = formulas;
		this.process();
	}
	
	protected void process() {
		if (mErrorPath.size() < 1) {
			return;
		}
		// -----------------------------------------------------------------------------------//
		// START: Yet another shot trying to find the actual error trace
		// --------------------//
		// -----------------------------------------------------------------------------------//
		CFGExplicitNode graphroot = (CFGExplicitNode)mErrorPath.get(0);
		HashMap<BoogieVar, CFGEdge> allEdgeIds = ((CFGEdge) graphroot
				.getOutgoingEdges().get(0)).getAllEdgeIds();
		ArrayList<ArrayList<CFGEdge>> takenEdges = new ArrayList<ArrayList<CFGEdge>>();
		INode startNode = null;
		for (int i = 0; i < mFormulas.length - 1; i++) {
			int indexOfEdgeOnPath = i * 2 + 3;
			ArrayList<CFGEdge> takenEdgesInReducedNode = new ArrayList<CFGEdge>();
			CFGEdge edge = (CFGEdge) mErrorPath.get(indexOfEdgeOnPath);
			for (BoogieVar bvar : allEdgeIds.keySet()) {
				SMTEdgeAnnotations annos = (SMTEdgeAnnotations) edge
						.getPayload().getAnnotations().get("SMT");
				if (annos.getOutVars().containsKey(bvar)) {
					CFGExplicitNode node = (CFGExplicitNode) mErrorPath
							.get(indexOfEdgeOnPath - 1);
					SCNodeAnnotations scAnnos = (SCNodeAnnotations) node
							.getPayload().getAnnotations().get("SC");
					Term tv = annos.getOutVars().get(bvar);
					Term constant = null;
					for (Term tmp_constant : scAnnos.getConstants().keySet()) {
						if (scAnnos.getConstants().get(tmp_constant) == tv) {
							constant = tmp_constant;
							break;
						}
					}
					Term value = this.getScript().getValue(new Term[] { constant })
							.get(constant);
					if (value == this.getScript().term("true")) {
						takenEdgesInReducedNode.add(allEdgeIds.get(bvar));
					}
				}
			}
			if (!takenEdgesInReducedNode.isEmpty()) {
				ArrayList<CFGEdge> sortedEdges = sortEdges(
						takenEdgesInReducedNode, startNode);
				takenEdges.add(sortedEdges);
				startNode = sortedEdges.get(sortedEdges.size() - 1).getTarget();
			}
		}
		// Get edges that are hidden in the error node
		CFGExplicitNode reducedErrorNode = (CFGExplicitNode) mErrorPath
				.get(mErrorPath.size() - 1);
		SCNodeAnnotations scAnnos = (SCNodeAnnotations) reducedErrorNode
				.getPayload().getAnnotations().get("SC");
		ArrayList<CFGEdge> takenEdgesInErrorNode = new ArrayList<CFGEdge>();
		for (Term constant : scAnnos.getConstants().keySet()) {
			if (scAnnos.getConstants().get(constant).getName()
					.contains("Ultimate")) {
				Term value = this.getScript().getValue(new Term[] { constant }).get(
						constant);
				if (value == this.getScript().term("true")) {
					takenEdgesInErrorNode.add(allEdgeIds.get(VariableSSAManager
							.getBoogieVariable(scAnnos.getConstants().get(
									constant))));
				}
			}
		}
		if (!takenEdgesInErrorNode.isEmpty()) {
			takenEdges.add(sortEdges(takenEdgesInErrorNode, startNode));
		}
		// -----------------------------------------------------------------------------------//
		// END: Yet another shot trying to find the actual error trace
		// ----------------------//
		// -----------------------------------------------------------------------------------//
//		Logger logger = UltimateServices.getInstance().getLogger(Activator.s_PLUGIN_ID);
		logger.info("Taken edges:");
		for (ArrayList<CFGEdge> edges: takenEdges) {
			for (CFGEdge edge: edges) {
				logger.info(edge.getTarget().getPayload().getName());
			}
		}
		collectEventSequence(takenEdges);
		// -----------------------------------------------------------------------------------//
		// START: This block collects all locations of the original error trace
		// (//TODO BETA)//
		// -----------------------------------------------------------------------------------//
//		ArrayList<AnnotatedTerm> termsOfAllTakenTransitions = new ArrayList<AnnotatedTerm>();
		for (ArrayList<CFGEdge> edgesOfReducedNode : takenEdges) {
			for (CFGEdge takenEdge : edgesOfReducedNode) {
				CFGExplicitNode targetNode = (CFGExplicitNode)takenEdge.getTarget();
				CFGNodeAnnotations cfgNodeAnnotations =
						(CFGNodeAnnotations)targetNode.getPayload().getAnnotations().get("CFGBuilder");
//				CFGNodeAnnotations cfgNodeAnnotations =
//						(CFGNodeAnnotations)takenEdge.getPayload().getAnnotations().get("CFGBuilder");
				if (cfgNodeAnnotations != null) {
					this.addAll(cfgNodeAnnotations.getStatements());
				}
//				if (this.get(this.size()-1) instanceof ReturnStatement) {
//					this.remove(this.size()-1);
//					return;
//				}
			}
		}
		// -----------------------------------------------------------------------------------//
		// END: This block collects all locations of the original error trace
		// ---------------//
		// -----------------------------------------------------------------------------------//
		return;
	}

	void collectEventSequence(ArrayList<ArrayList<CFGEdge>> takenEdges) {
		ArrayDeque<String> eventSequence = new ArrayDeque<String>();
		for (ArrayList<CFGEdge> edges : takenEdges) {
			CFGEdge entryEdge = edges.get(0);
			INode entryNode = entryEdge.getSource();
			String entryName = entryNode.getPayload().getName();
			if (entryName.contains("Event")) {
				entryName = (String) entryName.subSequence(1, entryName.indexOf("_"));
				eventSequence.add(entryName);
			}
			for (int i = 1; i < edges.size(); i++) {
				CFGEdge takenEdge = edges.get(i);
				INode node = takenEdge.getSource();
				String name = node.getPayload().getName();
				if (name.contains("Event")) {
					name = (String) name.subSequence(1, name.indexOf("_"));
					if (!(name.equals(eventSequence.peekLast())))
							eventSequence.add(name);
				}
			}
		}
		logger.info("Event Sequence: " + eventSequence.toString());
	}
	
	private ArrayList<CFGEdge> sortEdges(ArrayList<CFGEdge> edges,
			INode startNode) {
		ArrayList<CFGEdge> sortedEdges = new ArrayList<CFGEdge>();
		if (edges == null || edges.isEmpty())
			return sortedEdges;
		// -----------------------------------------------------------------------------------//
		// START: This block put all original cfg edges in the right order
		// ------------------//
		// -----------------------------------------------------------------------------------//
		/*
		 * put edges in the right order. First loop finds entry edge of the
		 * first reduced node. Second loop puts all others in order by iterating
		 * over the outgoing edges of the last edge in the order array.
		 */
		if (startNode == null) {
			for (CFGEdge currentEdge : edges) {
				boolean isEntry = true;
				for (CFGEdge nextEdge : edges) {
					if (currentEdge.getSource().equals(nextEdge.getTarget())) {
						isEntry = false;
						break;
					}
				}
				if (isEntry) {
					sortedEdges.add(currentEdge);
					break;
				}
			}
		} else {
			for (CFGEdge currentEdge : edges) {
				if (currentEdge.getSource().equals(startNode)) {
					sortedEdges.add(currentEdge);
					break;
				}
			}
		}

		while (true) {
			CFGEdge currentLastEdge = sortedEdges.get(sortedEdges.size() - 1);
			if (edges.size() == sortedEdges.size())
				break;
			for (IEdge nextEdge : edges) {
				if (nextEdge.getSource().equals(currentLastEdge.getTarget())) {
					sortedEdges.add((CFGEdge) nextEdge);
					break;
				}
			}
		}

		// -----------------------------------------------------------------------------------//
		// End: This block put all original cfg edges in the right order
		// --------------------//
		// -----------------------------------------------------------------------------------//

		return sortedEdges;
	}

	public ArrayList<IElement> getErrorPath() {
		return mErrorPath;
	}
	
	public Term[] getFormulas() {
		return mFormulas;
	}
	
	public IElement getGraphroot() {
		return mErrorPath.get(0);
	}
	
	public Procedure getProcedure() {
		CFGExplicitNode procNode = (CFGExplicitNode) mErrorPath.get(2);
		CFGNodeAnnotations cfgNodeAnnotations = 
				(CFGNodeAnnotations)procNode.getPayload().getAnnotations().get("procedure");
		return cfgNodeAnnotations.getProcedure();
	}
}
