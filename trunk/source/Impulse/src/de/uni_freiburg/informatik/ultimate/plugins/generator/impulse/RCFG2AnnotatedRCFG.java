package de.uni_freiburg.informatik.ultimate.plugins.generator.impulse;

import java.util.ArrayDeque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.model.IEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;

public class RCFG2AnnotatedRCFG {
	
	private SmtManager m_smtManager;
	
	public RCFG2AnnotatedRCFG(SmtManager smtMan) {
		m_smtManager = smtMan;
	}
	
	
	public ImpRootNode convert(RootNode oldRoot) {
		
		ImpRootNode newRoot = new ImpRootNode(oldRoot.getRootAnnot());
		
		ArrayDeque<ProgramPoint> openNodes = new ArrayDeque<ProgramPoint>();
		HashMap<ProgramPoint, AnnotatedProgramPoint> oldPpTonew = 
				new HashMap<ProgramPoint, AnnotatedProgramPoint>();
		
		
		for (RCFGEdge rootEdge : oldRoot.getOutgoingEdges()) {
			ProgramPoint oldNode = (ProgramPoint) rootEdge.getTarget();
			AnnotatedProgramPoint newNode = copyNode(oldNode);
			
			newRoot.addOutgoingNode(newNode, null);
			//new RootEdge(newRoot, newNode);
			openNodes.add(oldNode);
			oldPpTonew.put(oldNode, newNode);
		}
		
		/* 
		 * collect all Nodes and create AnnotatedProgramPoints
		 */
		HashSet<Return> returns = new HashSet<Return>();
		while (!openNodes.isEmpty()) {
			ProgramPoint currentNode = openNodes.pollFirst();
			
			for (RCFGEdge outEdge : currentNode.getOutgoingEdges()) {
				if (outEdge instanceof Return) {
					returns.add((Return) outEdge);
				}
				ProgramPoint newNode = (ProgramPoint) outEdge.getTarget();
				if (oldPpTonew.containsKey(newNode))
					continue;
				oldPpTonew.put(newNode, copyNode(newNode));
				openNodes.add(newNode);
			}
		}
		
		/*
		 *  put edges into annotated program points
		 */
		for (Entry<ProgramPoint, AnnotatedProgramPoint> entry  : oldPpTonew.entrySet()) {
			for (RCFGEdge outEdge : entry.getKey().getOutgoingEdges()) {
				AnnotatedProgramPoint annotatedTarget = 
						(AnnotatedProgramPoint) oldPpTonew.get(outEdge.getTarget());
				entry.getValue().addOutgoingNode(
				  annotatedTarget, (CodeBlock) outEdge);
//				annotatedTarget.addIncomingNode(
//						entry.getValue(), (CodeBlock) outEdge);
				if (outEdge instanceof Return) {
					AnnotatedProgramPoint callPredApp = oldPpTonew.get(((Return) outEdge).getCallerNode());
					entry.getValue().addOutGoingReturnCallPred(annotatedTarget, callPredApp);
				}
			}
		}
		return newRoot;
	}

	private AnnotatedProgramPoint copyNode(ProgramPoint pp) {
		return new AnnotatedProgramPoint(m_smtManager.newTruePredicate(), pp);
	}
}
