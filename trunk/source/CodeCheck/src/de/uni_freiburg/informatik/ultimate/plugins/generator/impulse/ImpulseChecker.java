package de.uni_freiburg.informatik.ultimate.plugins.generator.impulse;

import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.Queue;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedRun;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.appgraph.AnnotatedProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.appgraph.AppEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.appgraph.AppHyperEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.appgraph.DummyCodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.appgraph.ImpRootNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck.CodeChecker;
import de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck.GlobalSettings;
import de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck.GraphWriter;
import de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck.preferences.CodeCheckPreferenceInitializer.RedirectionStrategy;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.EdgeChecker;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.PredicateUnifier;

public class ImpulseChecker extends CodeChecker {
	
	//private HashMap <AnnotatedProgramPoint, AnnotatedProgramPoint> _cloneNode;
	
	private final RedirectionFinder cloneFinder;
	private int nodeIDs;
	
	public ImpulseChecker(IElement root, SmtManager m_smtManager, TAPreferences m_taPrefs, RootNode m_originalRoot, ImpRootNode m_graphRoot,
			GraphWriter m_graphWriter, EdgeChecker edgeChecker, PredicateUnifier predicateUnifier, Logger logger) {
		super(root, m_smtManager, m_taPrefs, m_originalRoot, m_graphRoot,
				m_graphWriter, edgeChecker, predicateUnifier, logger);
		cloneFinder = new RedirectionFinder(this);
		nodeIDs = 0;
	}
	
	public void replaceEdge(AppEdge edge, AnnotatedProgramPoint newTarget) {
		if (edge instanceof AppHyperEdge)
			edge.getSource().connectOutgoingReturn(((AppHyperEdge) edge).getHier(), (Return) edge.getStatement(), newTarget);
		else
			edge.getSource().connectOutgoing(edge.getStatement(), newTarget);

		edge.disconnect();
	}
	
	public boolean defaultRedirecting(AnnotatedProgramPoint[] nodes, AnnotatedProgramPoint[] clones) {
		
		boolean errorReached = false;
		for (int i = 0; i + 1 < nodes.length; ++i) {
			if (nodes[i + 1].isErrorLocation()) {
				clones[i].getEdge(nodes[i + 1]).disconnect();
				errorReached = true;
			} else {
				if (GlobalSettings._instance.defaultRedirection) {
					if (GlobalSettings._instance.checkSatisfiability)
						redirectIfValid(clones[i].getEdge(nodes[i + 1]), clones[i + 1]);
					else
						replaceEdge(clones[i].getEdge(nodes[i + 1]), clones[i + 1]);
				} else {
					AnnotatedProgramPoint clone = clones[i + 1];
					AppEdge prevEdge = clones[i].getEdge(nodes[i + 1]);
					if (GlobalSettings._instance.redirectionStrategy != RedirectionStrategy.No_Strategy)
						clone = cloneFinder.getStrongestValidCopy(prevEdge);
	
					if (clone == null)
						continue;
					redirectIfValid(prevEdge, clone);
				}
			}
		}
		
		return errorReached;
	}

	public boolean redirectEdges(AnnotatedProgramPoint[] nodes, AnnotatedProgramPoint[] clones) {

		for (int i = 0; i < nodes.length; ++i) {
			if (nodes[i].isErrorLocation())
				continue;
			AppEdge[] prevEdges = nodes[i].getIncomingEdges().toArray(new AppEdge[]{});
			for (AppEdge prevEdge : prevEdges) {
				AnnotatedProgramPoint clone = clones[i];
				
				if (GlobalSettings._instance.redirectionStrategy != RedirectionStrategy.No_Strategy)
					clone = cloneFinder.getStrongestValidCopy(prevEdge);
				
				if (clone == null)
					continue;
				redirectIfValid(prevEdge, clone);
			}
		}
		return true;
	}
	protected void redirectIfValid(AppEdge edge, AnnotatedProgramPoint target) {
		if (edge.getTarget() == target)
			return ;
		if (isValidRedirection(edge, target)) {
			if (edge instanceof AppHyperEdge) {
				
				if (!GlobalSettings._instance.checkSatisfiability || m_smtManager.isInductiveReturn(edge.getSource().getPredicate(), ((AppHyperEdge) edge).getHier().getPredicate(),
						(Return) edge.getStatement(), m_predicateUnifier.getFalsePredicate()) != LBool.UNSAT)	
					edge.getSource().connectOutgoingReturn(((AppHyperEdge) edge).getHier(), (Return) edge.getStatement(), target);
			} else {
				
				boolean result = !GlobalSettings._instance.checkSatisfiability;
				if (!result) {
					if (edge.getStatement() instanceof Call)
						result = m_smtManager.isInductiveCall(edge.getSource().getPredicate(), (Call) edge.getStatement(),
								m_predicateUnifier.getFalsePredicate()) != LBool.UNSAT;
					else
						result = m_smtManager.isInductive(edge.getSource().getPredicate(), edge.getStatement(),
							m_predicateUnifier.getFalsePredicate()) != LBool.UNSAT;
				}
				
				if (result)
					edge.getSource().connectOutgoing(edge.getStatement(), target);
				
			}
		
			edge.disconnect();
		}
	}
	public boolean isValidRedirection(AppEdge edge, AnnotatedProgramPoint target) {
		if (edge instanceof AppHyperEdge) {
			return isValidReturnEdge(edge.getSource(), edge.getStatement(), target,((AppHyperEdge) edge).getHier());
		} else {
			return isValidEdge(edge.getSource(), edge.getStatement(), target);
		}
	}
	@Override
	public boolean codeCheck(
			NestedRun<CodeBlock, AnnotatedProgramPoint> errorRun,
			IPredicate[] interpolants, AnnotatedProgramPoint procedureRoot) {

		AnnotatedProgramPoint[] nodes = errorRun.getStateSequence().toArray(new AnnotatedProgramPoint[0]);
		
		/*
		System.err.println("vor DFS");
		visited = new HashSet<AnnotatedProgramPoint>();
		dfsDEBUG(m_graphRoot, true);
		System.err.println(String.format("Graph nodes: %s\n", visited));
		System.err.println("Nach DFS");
		

		 
		ArrayList<AnnotatedProgramPoint> path = new ArrayList<AnnotatedProgramPoint>();
		Collections.addAll(path, nodes);
		System.err.println(String.format("Nodes: %s", path));

		ArrayList<IPredicate> interpolantsDBG = new ArrayList<IPredicate>();
		Collections.addAll(interpolantsDBG, interpolants);
		System.err.println(String.format("Inters: %s\n", interpolantsDBG));
		
		*/
		AnnotatedProgramPoint[] clones = new AnnotatedProgramPoint[nodes.length];
		//_cloneNode = new HashMap <AnnotatedProgramPoint, AnnotatedProgramPoint>();
		
		AnnotatedProgramPoint newRoot = new AnnotatedProgramPoint(nodes[0], nodes[0].getPredicate(), true, ++nodeIDs);
		
		clones[0] = nodes[0];
		//_cloneNode.put(newRoot, nodes[0]);
		nodes[0] = newRoot;
		
		for (int i = 0; i < interpolants.length; ++i) {
			//_cloneNode.put(nodes[i + 1], new AnnotatedProgramPoint(nodes[i + 1], conjugatePredicates(nodes[i + 1].getPredicate(), interpolants[i]), true));
			clones[i + 1] = new AnnotatedProgramPoint(nodes[i + 1], conjugatePredicates(nodes[i + 1].getPredicate(), interpolants[i]), true, ++nodeIDs);
		}
		
		if (!defaultRedirecting(nodes, clones))
			throw new AssertionError("The error location hasn't been reached.");
		//improveAnnotations(newRoot);
		redirectEdges(nodes, clones);
		
		if (GlobalSettings._instance.removeFalseNodes)
			removeFalseNodes(nodes, clones);
		
		return true;
	}
	
	public boolean removeFalseNodes(AnnotatedProgramPoint[] nodes, AnnotatedProgramPoint[] clones) {
		for (int i = 0; i < nodes.length; ++i) {
			if (nodes[i].isErrorLocation())
				continue;
            // TODO: Handle the false predicate properly.
			//if (clones[i].getPredicate().toString().endsWith("false"))
			IPredicate annotation = clones[i].getPredicate();
			if (m_predicateUnifier.getOrConstructPredicate(annotation.getFormula(), annotation.getVars(), annotation.getProcedures())
		        .equals(m_predicateUnifier.getFalsePredicate()))
				clones[i].isolateNode();
		}
		return true;
	}
	
	public boolean improveAnnotations(AnnotatedProgramPoint root) {
		HashSet <AnnotatedProgramPoint> seen = new HashSet <AnnotatedProgramPoint>();

		HashSet <AnnotatedProgramPoint> pushed = new HashSet <AnnotatedProgramPoint>();
		Queue <AnnotatedProgramPoint> queue = new LinkedList<AnnotatedProgramPoint>();
		
		queue.add(root);
		pushed.add(root);
		
		while (!queue.isEmpty()) {
			AnnotatedProgramPoint peak = queue.poll();
			AnnotatedProgramPoint[] prevNodes = peak.getIncomingNodes().toArray(new AnnotatedProgramPoint[]{});
			if (prevNodes.length == 1) {
				//TODO: Modify the new predicate.
				AnnotatedProgramPoint prevNode = prevNodes[0];
				if (seen.contains(prevNode)) {
					// peak.predicate &= prevNode.predicate o edge.formula
				}
			} else {
				//TODO: To handle this case later
				// Formula = false;
				for (AnnotatedProgramPoint prevNode : prevNodes) {
					if (seen.contains(prevNode)) {
						// Formula |= prevNode.predicate o edge.formula
					}
				}
				// peak.predicate &= Formula;
			}
			
			AnnotatedProgramPoint[] nextNodes = peak.getOutgoingNodes().toArray(new AnnotatedProgramPoint[]{});
			for (AnnotatedProgramPoint nextNode : nextNodes) {
				if (!pushed.contains(nextNode)) {
					pushed.add(nextNode);
					queue.add(nextNode);
				}
			}
			seen.add(peak);
		}
		
		return true;
	}
	

	public boolean isValidEdge(AnnotatedProgramPoint sourceNode, CodeBlock edgeLabel,
			AnnotatedProgramPoint destinationNode) {
		if (edgeLabel instanceof DummyCodeBlock)
			return false;
		// System.out.print(".");
		

		if (GlobalSettings._instance._memoizeNormalEdgeChecks) {
			if (_satTriples.get(sourceNode.getPredicate()) != null && _satTriples.get(sourceNode.getPredicate()).get(edgeLabel) != null
					&& _satTriples.get(sourceNode.getPredicate()).get(edgeLabel).contains(destinationNode.getPredicate())) {
				memoizationHitsSat++;
				return true;
			}
			if (_unsatTriples.get(sourceNode.getPredicate()) != null && _unsatTriples.get(sourceNode.getPredicate()).get(edgeLabel) != null
					&& _unsatTriples.get(sourceNode.getPredicate()).get(edgeLabel).contains(destinationNode.getPredicate())) {
				memoizationHitsUnsat++;
				return false;
			}
		}

		boolean result = true;
		if (edgeLabel instanceof Call)
			result = m_smtManager.isInductiveCall(sourceNode.getPredicate(), (Call) edgeLabel,
					destinationNode.getPredicate()) == LBool.UNSAT;
		else
			result = m_smtManager.isInductive(sourceNode.getPredicate(), edgeLabel, destinationNode.getPredicate()) == LBool.UNSAT;
	

		if (GlobalSettings._instance._memoizeNormalEdgeChecks)
			if (result)
				addSatTriple(sourceNode.getPredicate(), edgeLabel, destinationNode.getPredicate());
			else
				addUnsatTriple(sourceNode.getPredicate(), edgeLabel, destinationNode.getPredicate());

		return result;
	}

	public boolean isValidReturnEdge(AnnotatedProgramPoint sourceNode, CodeBlock edgeLabel,
			AnnotatedProgramPoint destinationNode, AnnotatedProgramPoint callNode) {
		if (GlobalSettings._instance._memoizeReturnEdgeChecks) {
			if (_satQuadruples.get(sourceNode.getPredicate()) != null && _satQuadruples.get(sourceNode.getPredicate()).get(callNode) != null
					&& _satQuadruples.get(sourceNode.getPredicate()).get(callNode).get(edgeLabel) != null
					&& _satQuadruples.get(sourceNode.getPredicate()).get(callNode).get(edgeLabel).contains(destinationNode.getPredicate())) {
				memoizationReturnHitsSat++;
				return true;
			}
			if (_unsatQuadruples.get(sourceNode.getPredicate()) != null && _unsatQuadruples.get(sourceNode.getPredicate()).get(callNode) != null
					&& _unsatQuadruples.get(sourceNode.getPredicate()).get(callNode).get(edgeLabel) != null
					&& _unsatQuadruples.get(sourceNode.getPredicate()).get(callNode).get(edgeLabel).contains(destinationNode.getPredicate())) {
				memoizationReturnHitsUnsat++;
				return false;
			}
		}

		boolean result = m_smtManager.isInductiveReturn(sourceNode.getPredicate(), callNode.getPredicate(), (Return) edgeLabel,
				destinationNode.getPredicate()) == LBool.UNSAT;

		if (GlobalSettings._instance._memoizeReturnEdgeChecks)
			if (result)
				addSatQuadruple(sourceNode.getPredicate(), callNode.getPredicate(), edgeLabel, destinationNode.getPredicate());
			else
				addUnsatQuadruple(sourceNode.getPredicate(), callNode.getPredicate(), edgeLabel, destinationNode.getPredicate());

		return result;
	}

	/*
	public boolean isStrongerPredicate(AnnotatedProgramPoint strongerNode, AnnotatedProgramPoint weakerNode) {
		return m_smtManager.isCovered(strongerNode.getPredicate(), weakerNode.getPredicate()) == LBool.UNSAT;
	}
	*/
	
	@Override
	public boolean codeCheck(NestedRun<CodeBlock, AnnotatedProgramPoint> errorRun, IPredicate[] interpolants,
			AnnotatedProgramPoint procedureRoot,
			HashMap<IPredicate, HashMap<CodeBlock, HashSet<IPredicate>>> satTriples,
			HashMap<IPredicate, HashMap<CodeBlock, HashSet<IPredicate>>> unsatTriples) {
		this._satTriples = satTriples;
		this._unsatTriples = unsatTriples;
		return this.codeCheck(errorRun, interpolants, procedureRoot);
	}

	@Override
	public boolean codeCheck(NestedRun<CodeBlock, AnnotatedProgramPoint> errorRun, IPredicate[] interpolants,
			AnnotatedProgramPoint procedureRoot,
			HashMap<IPredicate, HashMap<CodeBlock, HashSet<IPredicate>>> satTriples,
			HashMap<IPredicate, HashMap<CodeBlock, HashSet<IPredicate>>> unsatTriples,
			HashMap<IPredicate, HashMap<IPredicate, HashMap<CodeBlock, HashSet<IPredicate>>>> satQuadruples,
			HashMap<IPredicate, HashMap<IPredicate, HashMap<CodeBlock, HashSet<IPredicate>>>> unsatQuadruples) {
		this._satQuadruples = satQuadruples;
		this._unsatQuadruples = unsatQuadruples;
		return this.codeCheck(errorRun, interpolants, procedureRoot, satTriples, unsatTriples);
	}
	
	
	

	protected boolean connectOutgoingIfValid(AnnotatedProgramPoint source, CodeBlock statement, AnnotatedProgramPoint target) {
		if (isValidEdge(source, statement, target)) {
			source.connectOutgoing(statement, target);
			return true;
		} else {
			return false;
		}
	}

	protected boolean connectOutgoingReturnIfValid(AnnotatedProgramPoint source, AnnotatedProgramPoint hier,
			Return statement, AnnotatedProgramPoint target) {
		if (isValidReturnEdge(source, statement, target, hier)) {
			source.connectOutgoingReturn(hier, statement, target);
			return true;
		} else {
			return false;
		}
	}
	
	HashSet <AnnotatedProgramPoint> visited;
	protected void dfsDEBUG(AnnotatedProgramPoint node, boolean print) {
		
		if (visited.contains(node))
			return ;
		visited.add(node);
		if (print) {
			System.err.println(String.format("\n%s\n", node));
			System.err.print("[ ");
			for (AppEdge nextEdge : node.getOutgoingEdges()) {
				System.err.print(" << " + (nextEdge instanceof AppHyperEdge ? ("return to " + ((AppHyperEdge) nextEdge).getHier()) : nextEdge.getStatement()) + " >> " + nextEdge.getTarget());
				System.err.print(" , ");
			}
			System.err.println("]");
			
			System.err.print("\nCopied From " + node.getParentCopy() + "\nCopies :: { ");
			for (AnnotatedProgramPoint copy : node.getNextClones()) {
				System.err.print(copy + " , ");
			}
			System.err.println("}");
		}
		for (AnnotatedProgramPoint nextNode : node.getOutgoingNodes()) {
			dfsDEBUG(nextNode, print);
		}
	}
	


	boolean isStrongerPredicate(AnnotatedProgramPoint node1,
			AnnotatedProgramPoint node2) {
		
		boolean result = m_predicateUnifier.getCoverageRelation().isCovered(node1.getPredicate(), node2.getPredicate()) == LBool.UNSAT;
		//System.err.printf("%s > %s  :: %s\n", predicate1, predicate2, result);
		if (result) {
			boolean converse = m_predicateUnifier.getCoverageRelation().isCovered(node2.getPredicate(), node1.getPredicate()) == LBool.UNSAT;
			result &= !converse || (converse && node1._nodeID > node2._nodeID);
		}
		return result;
	}
}
