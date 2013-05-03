package de.uni_freiburg.informatik.ultimate.plugins.generator.impulse;

import java.util.ArrayDeque;
import java.util.ArrayList;
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
	
	HashMap<AnnotatedProgramPoint, ArrayList<AnnotatedProgramPoint>> m_callPredToReturnPreds;
	
	HashMap<ProgramPoint, AnnotatedProgramPoint> m_oldPpTonew;
				
	public RCFG2AnnotatedRCFG(SmtManager smtMan) {
		m_smtManager = smtMan;
	}
	
	public ImpRootNode convert(RootNode oldRoot) {
		m_callPredToReturnPreds =
				new HashMap<AnnotatedProgramPoint, ArrayList<AnnotatedProgramPoint>>();
		ImpRootAnnot ira = new ImpRootAnnot(oldRoot.getRootAnnot().getTaPrefs(),
				oldRoot.getRootAnnot().getBoogie2SMT(), null, m_callPredToReturnPreds);
		
		ImpRootNode newRoot = new ImpRootNode(ira);

		
		ArrayDeque<ProgramPoint> openNodes = new ArrayDeque<ProgramPoint>();
		m_oldPpTonew = 
				new HashMap<ProgramPoint, AnnotatedProgramPoint>();
		
		
		for (RCFGEdge rootEdge : oldRoot.getOutgoingEdges()) {
			ProgramPoint oldNode = (ProgramPoint) rootEdge.getTarget();
			AnnotatedProgramPoint newNode = copyNode(oldNode);
			
			newRoot.connectOutgoing(newNode, new DummyCodeBlock());
			//new RootEdge(newRoot, newNode);
			openNodes.add(oldNode);
			m_oldPpTonew.put(oldNode, newNode);
		}
		
		/* 
		 * collect all Nodes and create AnnotatedProgramPoints
		 */
//		HashSet<Return> returns = new HashSet<Return>();
		while (!openNodes.isEmpty()) {
			ProgramPoint currentNode = openNodes.pollFirst();
			
			for (RCFGEdge outEdge : currentNode.getOutgoingEdges()) {
//				if (outEdge instanceof Return) {
//					returns.add((Return) outEdge);
//				}
				ProgramPoint newNode = (ProgramPoint) outEdge.getTarget();
				if (m_oldPpTonew.containsKey(newNode))
					continue;
				m_oldPpTonew.put(newNode, copyNode(newNode));
				openNodes.add(newNode);
			}
		}
		
		/*
		 *  put edges into annotated program points
		 */
		for (Entry<ProgramPoint, AnnotatedProgramPoint> entry  : m_oldPpTonew.entrySet()) {
			for (RCFGEdge outEdge : entry.getKey().getOutgoingEdges()) {
				AnnotatedProgramPoint annotatedTarget = 
						(AnnotatedProgramPoint) m_oldPpTonew.get(outEdge.getTarget());
				entry.getValue().connectOutgoing(
				  annotatedTarget, (CodeBlock) outEdge);
//				annotatedTarget.addIncomingNode(
//						entry.getValue(), (CodeBlock) outEdge);
				if (outEdge instanceof Return) {//add annotation needed for return edge duplication
					AnnotatedProgramPoint callPredApp = m_oldPpTonew.get(((Return) outEdge).getCallerProgramPoint());
					entry.getValue().addOutGoingReturnCallPred(annotatedTarget, callPredApp);
					updateCallPredToReturnPreds(callPredApp, entry.getValue());
				}
			}
		}
		return newRoot;
	}

	private AnnotatedProgramPoint copyNode(ProgramPoint pp) {
		return new AnnotatedProgramPoint(m_smtManager.newTruePredicate(), pp);
	}
	
	private void updateCallPredToReturnPreds(AnnotatedProgramPoint callPred, AnnotatedProgramPoint returnPred) {
		ArrayList<AnnotatedProgramPoint> returnPreds = m_callPredToReturnPreds.get(callPred);
		if (returnPreds == null)
			returnPreds = new ArrayList<AnnotatedProgramPoint>();
		returnPreds.add(returnPred);
		m_callPredToReturnPreds.put(callPred, returnPreds);
	}
	
	public HashMap<ProgramPoint, AnnotatedProgramPoint> getOldPpTonew() {
		return m_oldPpTonew;
	}
}
