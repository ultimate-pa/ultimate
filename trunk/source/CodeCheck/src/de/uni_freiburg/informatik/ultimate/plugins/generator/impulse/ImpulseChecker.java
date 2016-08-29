/*
 * Copyright (C) 2014-2015 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2014-2015 Mostafa Mahmoud Amin
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
package de.uni_freiburg.informatik.ultimate.plugins.generator.impulse;

import java.util.HashSet;
import java.util.LinkedList;
import java.util.Queue;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedRun;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.ICallAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IInternalAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IReturnAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hoaretriple.IHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hoaretriple.IHoareTripleChecker.Validity;
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
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.PredicateUnifier;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.IsContained;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap3;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap4;

public class ImpulseChecker extends CodeChecker {
	
	//private HashMap <AnnotatedProgramPoint, AnnotatedProgramPoint> _cloneNode;
	
	private final RedirectionFinder cloneFinder;
	private int nodeIDs;
	
	public ImpulseChecker(IElement root, SmtManager msmtManager, RootNode moriginalRoot, ImpRootNode mgraphRoot,
			GraphWriter mgraphWriter, IHoareTripleChecker edgeChecker, PredicateUnifier predicateUnifier, ILogger logger) {
		super(root, msmtManager, moriginalRoot, mgraphRoot,
				mgraphWriter, edgeChecker, predicateUnifier, logger);
		cloneFinder = new RedirectionFinder(this);
		nodeIDs = 0;
	}
	
	public void replaceEdge(AppEdge edge, AnnotatedProgramPoint newTarget) {
		if (edge instanceof AppHyperEdge) {
			edge.getSource().connectOutgoingReturn(((AppHyperEdge) edge).getHier(), (Return) edge.getStatement(), newTarget);
		} else {
			edge.getSource().connectOutgoing(edge.getStatement(), newTarget);
		}

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
					if (GlobalSettings._instance.checkSatisfiability) {
						redirectIfValid(clones[i].getEdge(nodes[i + 1]), clones[i + 1]);
					} else {
						replaceEdge(clones[i].getEdge(nodes[i + 1]), clones[i + 1]);
					}
				} else {
					AnnotatedProgramPoint clone = clones[i + 1];
					final AppEdge prevEdge = clones[i].getEdge(nodes[i + 1]);
					if (GlobalSettings._instance.redirectionStrategy != RedirectionStrategy.No_Strategy) {
						clone = cloneFinder.getStrongestValidCopy(prevEdge);
					}
	
					if (clone == null) {
						continue;
					}
					redirectIfValid(prevEdge, clone);
				}
			}
		}
		
		return errorReached;
	}

	public boolean redirectEdges(AnnotatedProgramPoint[] nodes, AnnotatedProgramPoint[] clones) {

		for (int i = 0; i < nodes.length; ++i) {
			if (nodes[i].isErrorLocation()) {
				continue;
			}
			final AppEdge[] prevEdges = nodes[i].getIncomingEdges().toArray(new AppEdge[]{});
			for (final AppEdge prevEdge : prevEdges) {
				AnnotatedProgramPoint clone = clones[i];
				
				if (GlobalSettings._instance.redirectionStrategy != RedirectionStrategy.No_Strategy) {
					clone = cloneFinder.getStrongestValidCopy(prevEdge);
				}
				
				if (clone == null) {
					continue;
				}
				redirectIfValid(prevEdge, clone);
			}
		}
		return true;
	}
	protected void redirectIfValid(AppEdge edge, AnnotatedProgramPoint target) {
		if (edge.getTarget() == target) {
			return ;
		}
		if (isValidRedirection(edge, target)) {
			if (edge instanceof AppHyperEdge) {
				
//				if (!GlobalSettings._instance.checkSatisfiability || msmtManager.isInductiveReturn(edge.getSource().getPredicate(), ((AppHyperEdge) edge).getHier().getPredicate(),
//						(Return) edge.getStatement(), mpredicateUnifier.getFalsePredicate()) != LBool.UNSAT)	
				if (!GlobalSettings._instance.checkSatisfiability || 
						_edgeChecker.checkReturn(edge.getSource().getPredicate(), ((AppHyperEdge) edge).getHier().getPredicate(), 
								(IReturnAction) edge.getStatement(), edge.getTarget().getPredicate())
						  != Validity.VALID) {
					;
				}
					edge.getSource().connectOutgoingReturn(((AppHyperEdge) edge).getHier(), (Return) edge.getStatement(), target);
			} else {
				
				boolean result = !GlobalSettings._instance.checkSatisfiability;
				if (!result) {
					if (edge.getStatement() instanceof Call) {
						//						result = msmtManager.isInductiveCall(edge.getSource().getPredicate(), (Call) edge.getStatement(),
//								mpredicateUnifier.getFalsePredicate()) != LBool.UNSAT;
						result = _edgeChecker.checkCall(edge.getSource().getPredicate(), (ICallAction) edge.getStatement(), 
								edge.getTarget().getPredicate())
								 != Validity.VALID;
					} else {
						//						result = msmtManager.isInductive(edge.getSource().getPredicate(), edge.getStatement(),
//							mpredicateUnifier.getFalsePredicate()) != LBool.UNSAT;
						result = _edgeChecker.checkInternal(edge.getSource().getPredicate(), (IInternalAction) edge.getStatement(), 
								edge.getTarget().getPredicate())
								!= Validity.VALID;
					}
				}
				
				if (result) {
					edge.getSource().connectOutgoing(edge.getStatement(), target);
				}
				
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

		final AnnotatedProgramPoint[] nodes = errorRun.getStateSequence().toArray(new AnnotatedProgramPoint[0]);
		
		/*
		System.err.println("vor DFS");
		visited = new HashSet<AnnotatedProgramPoint>();
		dfsDEBUG(mgraphRoot, true);
		System.err.println(String.format("Graph nodes: %s\n", visited));
		System.err.println("Nach DFS");
		

		 
		ArrayList<AnnotatedProgramPoint> path = new ArrayList<AnnotatedProgramPoint>();
		Collections.addAll(path, nodes);
		System.err.println(String.format("Nodes: %s", path));

		ArrayList<IPredicate> interpolantsDBG = new ArrayList<IPredicate>();
		Collections.addAll(interpolantsDBG, interpolants);
		System.err.println(String.format("Inters: %s\n", interpolantsDBG));
		
		*/
		final AnnotatedProgramPoint[] clones = new AnnotatedProgramPoint[nodes.length];
		//_cloneNode = new HashMap <AnnotatedProgramPoint, AnnotatedProgramPoint>();
		
		final AnnotatedProgramPoint newRoot = new AnnotatedProgramPoint(nodes[0], nodes[0].getPredicate(), true, ++nodeIDs);
		
		clones[0] = nodes[0];
		//_cloneNode.put(newRoot, nodes[0]);
		nodes[0] = newRoot;
		
		for (int i = 0; i < interpolants.length; ++i) {
			//_cloneNode.put(nodes[i + 1], new AnnotatedProgramPoint(nodes[i + 1], conjugatePredicates(nodes[i + 1].getPredicate(), interpolants[i]), true));
			clones[i + 1] = new AnnotatedProgramPoint(nodes[i + 1], conjugatePredicates(nodes[i + 1].getPredicate(), interpolants[i]), true, ++nodeIDs);
		}
		
		if (!defaultRedirecting(nodes, clones)) {
			throw new AssertionError("The error location hasn't been reached.");
		}
		//improveAnnotations(newRoot);
		redirectEdges(nodes, clones);
		
		if (GlobalSettings._instance.removeFalseNodes) {
			removeFalseNodes(nodes, clones);
		}
		
		return true;
	}
	
	public boolean removeFalseNodes(AnnotatedProgramPoint[] nodes, AnnotatedProgramPoint[] clones) {
		for (int i = 0; i < nodes.length; ++i) {
			if (nodes[i].isErrorLocation()) {
				continue;
			}
            // TODO: Handle the false predicate properly.
			//if (clones[i].getPredicate().toString().endsWith("false"))
			final IPredicate annotation = clones[i].getPredicate();
			if (mpredicateUnifier.getOrConstructPredicate(annotation.getFormula())
		        .equals(mpredicateUnifier.getFalsePredicate())) {
				clones[i].isolateNode();
			}
		}
		return true;
	}
	
	public boolean improveAnnotations(AnnotatedProgramPoint root) {
		final HashSet <AnnotatedProgramPoint> seen = new HashSet <AnnotatedProgramPoint>();

		final HashSet <AnnotatedProgramPoint> pushed = new HashSet <AnnotatedProgramPoint>();
		final Queue <AnnotatedProgramPoint> queue = new LinkedList<AnnotatedProgramPoint>();
		
		queue.add(root);
		pushed.add(root);
		
		while (!queue.isEmpty()) {
			final AnnotatedProgramPoint peak = queue.poll();
			final AnnotatedProgramPoint[] prevNodes = peak.getIncomingNodes().toArray(new AnnotatedProgramPoint[]{});
			if (prevNodes.length == 1) {
				//TODO: Modify the new predicate.
				final AnnotatedProgramPoint prevNode = prevNodes[0];
				if (seen.contains(prevNode)) {
					// peak.predicate &= prevNode.predicate o edge.formula
				}
			} else {
				//TODO: To handle this case later
				// Formula = false;
				for (final AnnotatedProgramPoint prevNode : prevNodes) {
					if (seen.contains(prevNode)) {
						// Formula |= prevNode.predicate o edge.formula
					}
				}
				// peak.predicate &= Formula;
			}
			
			final AnnotatedProgramPoint[] nextNodes = peak.getOutgoingNodes().toArray(new AnnotatedProgramPoint[]{});
			for (final AnnotatedProgramPoint nextNode : nextNodes) {
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
		 {
			return false;
		// System.out.print(".");
		}
		

		if (GlobalSettings._instance._memoizeNormalEdgeChecks) {
			if (_satTriples.get(sourceNode.getPredicate(), edgeLabel, destinationNode.getPredicate()) == IsContained.IsContained) {
				memoizationHitsSat++;
				return true;
			}
			if (_unsatTriples.get(sourceNode.getPredicate(), edgeLabel, destinationNode.getPredicate()) == IsContained.IsContained) {
				memoizationHitsUnsat++;
				return false;
			}
		}

		boolean result = true;
		if (edgeLabel instanceof Call) {
			result = _edgeChecker.checkCall(sourceNode.getPredicate(), (ICallAction) edgeLabel, destinationNode.getPredicate()) == Validity.VALID;
		} else {
			result = _edgeChecker.checkInternal(sourceNode.getPredicate(), (IInternalAction) edgeLabel, destinationNode.getPredicate()) == Validity.VALID;
		}
	

		if (GlobalSettings._instance._memoizeNormalEdgeChecks) {
			if (result) {
				_satTriples.put(sourceNode.getPredicate(), edgeLabel, destinationNode.getPredicate(), IsContained.IsContained);
			} else {
				_unsatTriples.put(sourceNode.getPredicate(), edgeLabel, destinationNode.getPredicate(), IsContained.IsContained);
			}
		}

		return result;
	}

	public boolean isValidReturnEdge(AnnotatedProgramPoint sourceNode, CodeBlock edgeLabel,
			AnnotatedProgramPoint destinationNode, AnnotatedProgramPoint callNode) {
		if (GlobalSettings._instance._memoizeReturnEdgeChecks) {
			if (_satQuadruples.get(sourceNode.getPredicate(), callNode.getPredicate(), edgeLabel, destinationNode.getPredicate()) 
					== IsContained.IsContained) {
				memoizationReturnHitsSat++;
				return true;
			}
			if (_unsatQuadruples.get(sourceNode.getPredicate(), callNode.getPredicate(), edgeLabel, destinationNode.getPredicate()) 
					== IsContained.IsContained) {
				memoizationReturnHitsUnsat++;
				return false;
			}
		}

		final boolean result = _edgeChecker.checkReturn(sourceNode.getPredicate(), callNode.getPredicate(), 
				(IReturnAction) edgeLabel, destinationNode.getPredicate())
				 == Validity.VALID;

		if (GlobalSettings._instance._memoizeReturnEdgeChecks) {
			if (result) {
				_satQuadruples.put(sourceNode.getPredicate(), callNode.getPredicate(), 
						edgeLabel, destinationNode.getPredicate(), IsContained.IsContained);
			} else {
				_unsatQuadruples.put(sourceNode.getPredicate(), callNode.getPredicate(), 
						edgeLabel, destinationNode.getPredicate(), IsContained.IsContained);
			}
		}

		return result;
	}

	/*
	public boolean isStrongerPredicate(AnnotatedProgramPoint strongerNode, AnnotatedProgramPoint weakerNode) {
		return msmtManager.isCovered(strongerNode.getPredicate(), weakerNode.getPredicate()) == LBool.UNSAT;
	}
	*/
	
	@Override
	public boolean codeCheck(NestedRun<CodeBlock, AnnotatedProgramPoint> errorRun, IPredicate[] interpolants,
			AnnotatedProgramPoint procedureRoot,
			NestedMap3<IPredicate, CodeBlock, IPredicate, IsContained> satTriples,
			NestedMap3<IPredicate, CodeBlock, IPredicate, IsContained> unsatTriples) {
		_satTriples = satTriples;
		_unsatTriples = unsatTriples;
		return this.codeCheck(errorRun, interpolants, procedureRoot);
	}

	@Override
	public boolean codeCheck(NestedRun<CodeBlock, AnnotatedProgramPoint> errorRun, IPredicate[] interpolants,
			AnnotatedProgramPoint procedureRoot,
			NestedMap3<IPredicate, CodeBlock, IPredicate, IsContained> satTriples,
			NestedMap3<IPredicate, CodeBlock, IPredicate, IsContained> unsatTriples,
			NestedMap4<IPredicate, IPredicate, CodeBlock, IPredicate, IsContained> satQuadruples,
			NestedMap4<IPredicate, IPredicate, CodeBlock, IPredicate, IsContained> unsatQuadruples) {
		_satQuadruples = satQuadruples;
		_unsatQuadruples = unsatQuadruples;
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
		
		if (visited.contains(node)) {
			return ;
		}
		visited.add(node);
		if (print) {
			System.err.println(String.format("\n%s\n", node));
			System.err.print("[ ");
			for (final AppEdge nextEdge : node.getOutgoingEdges()) {
				System.err.print(" << " + (nextEdge instanceof AppHyperEdge ? ("return to " + ((AppHyperEdge) nextEdge).getHier()) : nextEdge.getStatement()) + " >> " + nextEdge.getTarget());
				System.err.print(" , ");
			}
			System.err.println("]");
			
			System.err.print("\nCopied From " + node.getParentCopy() + "\nCopies :: { ");
			for (final AnnotatedProgramPoint copy : node.getNextClones()) {
				System.err.print(copy + " , ");
			}
			System.err.println("}");
		}
		for (final AnnotatedProgramPoint nextNode : node.getOutgoingNodes()) {
			dfsDEBUG(nextNode, print);
		}
	}
	


	boolean isStrongerPredicate(AnnotatedProgramPoint node1,
			AnnotatedProgramPoint node2) {
		
		boolean result = mpredicateUnifier.getCoverageRelation().isCovered(node1.getPredicate(), node2.getPredicate()) == Validity.VALID;
		//System.err.printf("%s > %s  :: %s\n", predicate1, predicate2, result);
		if (result) {
			final boolean converse = mpredicateUnifier.getCoverageRelation().isCovered(node2.getPredicate(), node1.getPredicate()) == Validity.VALID;
			result &= !converse || (converse && node1._nodeID > node2._nodeID);
		}
		return result;
	}
}
