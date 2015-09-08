/*
 * Copyright (C) 2014-2015 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE CodeCheck plug-in.
 * 
 * The ULTIMATE CodeCheck plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE CodeCheck plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE CodeCheck plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE CodeCheck plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE CodeCheck plug-in grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.appgraph;

import java.util.ArrayDeque;
import java.util.HashMap;
import java.util.Map.Entry;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootAnnot;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;

public class RCFG2AnnotatedRCFG {

	// HashMap<AnnotatedProgramPoint, ArrayList<AnnotatedProgramPoint>>
	// m_callPredToReturnPreds;

	HashMap<ProgramPoint, AnnotatedProgramPoint> m_oldPpTonew;
	private final Logger mLogger;

	public RCFG2AnnotatedRCFG(SmtManager smtMan, Logger logger) {
		mLogger = logger;
	}

	public ImpRootNode convert(IUltimateServiceProvider mServices, RootNode oldRoot, IPredicate truePredicate) {
		// m_callPredToReturnPreds =
		// new HashMap<AnnotatedProgramPoint,
		// ArrayList<AnnotatedProgramPoint>>();
		// ImpRootAnnot ira = new
		// ImpRootAnnot(oldRoot.getRootAnnot().getBoogieDeclarations(),
		// oldRoot.getRootAnnot().getBoogie2SMT(), null); //,
		// m_callPredToReturnPreds);
		RootAnnot ra = new RootAnnot(mServices, oldRoot.getRootAnnot().getBoogieDeclarations(), // FIXME:
																						// do
																						// we
																						// need
																						// a
																						// new
																						// rootannot??
				oldRoot.getRootAnnot().getBoogie2SMT(), null);

		ImpRootNode newRoot = new ImpRootNode(ra);

		ArrayDeque<ProgramPoint> openNodes = new ArrayDeque<ProgramPoint>();
		m_oldPpTonew = new HashMap<ProgramPoint, AnnotatedProgramPoint>();

		for (RCFGEdge rootEdge : oldRoot.getOutgoingEdges()) {
			ProgramPoint oldNode = (ProgramPoint) rootEdge.getTarget();
			AnnotatedProgramPoint newNode = copyNode(oldNode, truePredicate);

			newRoot.connectOutgoing(new DummyCodeBlock(mLogger), newNode);
			// new RootEdge(newRoot, newNode);
			openNodes.add(oldNode);
			m_oldPpTonew.put(oldNode, newNode);
		}

		/*
		 * collect all Nodes and create AnnotatedProgramPoints
		 */
		// HashSet<Return> returns = new HashSet<Return>();
		while (!openNodes.isEmpty()) {
			ProgramPoint currentNode = openNodes.pollFirst();

			for (RCFGEdge outEdge : currentNode.getOutgoingEdges()) {
				// if (outEdge instanceof Return) {
				// returns.add((Return) outEdge);
				// }
				ProgramPoint newNode = (ProgramPoint) outEdge.getTarget();
				if (m_oldPpTonew.containsKey(newNode))
					continue;
				m_oldPpTonew.put(newNode, copyNode(newNode, truePredicate));
				openNodes.add(newNode);
				if (outEdge instanceof Return) {
					ProgramPoint hier = ((Return) outEdge).getCallerProgramPoint();
					if (m_oldPpTonew.containsKey(hier))
						continue;
					m_oldPpTonew.put(hier, copyNode(hier, truePredicate));
					openNodes.add(hier);
				}
			}
		}

		/*
		 * put edges into annotated program points
		 */
		for (Entry<ProgramPoint, AnnotatedProgramPoint> entry : m_oldPpTonew.entrySet()) {
			for (RCFGEdge outEdge : entry.getKey().getOutgoingEdges()) {
				AnnotatedProgramPoint annotatedTarget = (AnnotatedProgramPoint) m_oldPpTonew.get(outEdge.getTarget());

				if (outEdge instanceof Return) {
					AnnotatedProgramPoint callPred = m_oldPpTonew.get(((Return) outEdge).getCallerProgramPoint());
					entry.getValue().connectOutgoingReturn(callPred, (Return) outEdge, annotatedTarget);
					// updateCallPredToReturnPreds(callPred, entry.getValue());
				} else {
					entry.getValue().connectOutgoing((CodeBlock) outEdge, annotatedTarget);
				}

				// entry.getValue().connectOutgoing(
				// annotatedTarget, (CodeBlock) outEdge);
				// // annotatedTarget.addIncomingNode(
				// // entry.getValue(), (CodeBlock) outEdge);
				// if (outEdge instanceof Return) {//add annotation needed for
				// return edge duplication
				// AnnotatedProgramPoint callPredApp =
				// m_oldPpTonew.get(((Return) outEdge).getCallerProgramPoint());
				// entry.getValue().addOutGoingReturnCallPred(annotatedTarget,
				// callPredApp);
				// updateCallPredToReturnPreds(callPredApp, entry.getValue());
				// }
			}
		}
		return newRoot;
	}

	private AnnotatedProgramPoint copyNode(ProgramPoint pp, IPredicate truePredicate) {
		return new AnnotatedProgramPoint(truePredicate, pp);
	}

	// private void updateCallPredToReturnPreds(AnnotatedProgramPoint callPred,
	// AnnotatedProgramPoint returnPred) {
	// ArrayList<AnnotatedProgramPoint> returnPreds =
	// m_callPredToReturnPreds.get(callPred);
	// if (returnPreds == null)
	// returnPreds = new ArrayList<AnnotatedProgramPoint>();
	// returnPreds.add(returnPred);
	// m_callPredToReturnPreds.put(callPred, returnPreds);
	// }

	public HashMap<ProgramPoint, AnnotatedProgramPoint> getOldPpTonew() {
		return m_oldPpTonew;
	}
}
