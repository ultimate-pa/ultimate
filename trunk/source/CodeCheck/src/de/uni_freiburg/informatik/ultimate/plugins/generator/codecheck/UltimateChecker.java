package de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck;

import java.util.AbstractCollection;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedRun;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWord;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.EdgeChecker;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.PredicateUnifier;

/**
 * UltimateChecker class, implements the model checker Ultimate.
 * 
 * @author Mostafa Mahmoud
 * 
 */
public class UltimateChecker extends CodeChecker {

	HashMap<AnnotatedProgramPoint, HashMap<CodeBlock, AnnotatedProgramPoint>> _pre2stm2post_toConnectIfSat;
	HashMap<AnnotatedProgramPoint, HashMap<AnnotatedProgramPoint, HashMap<Return, AnnotatedProgramPoint>>> _pre2hier2stm2post_toConnectIfSat;
	private HashMap<IPredicate,HashMap<CodeBlock,HashSet<IPredicate>>> _satTriples;
	private HashMap<IPredicate,HashMap<CodeBlock,HashSet<IPredicate>>> _unsatTriples;
	private boolean _memoizeNormalEdgeChecks = false;
	

	
	public UltimateChecker(IElement root, SmtManager m_smtManager,
			IPredicate m_truePredicate, IPredicate m_falsePredicate,
			TAPreferences m_taPrefs, RootNode m_originalRoot,
			ImpRootNode m_graphRoot, GraphWriter m_graphWriter, EdgeChecker edgeChecker, PredicateUnifier predicateUnifier) {
		super(root, m_smtManager, m_truePredicate, m_falsePredicate, m_taPrefs,
				m_originalRoot, m_graphRoot, m_graphWriter, edgeChecker, predicateUnifier);
	}

	private void splitNode_Normal(AnnotatedProgramPoint oldNode, IPredicate predicate) {
		//make two new nodes
		AnnotatedProgramPoint newNode1 = new AnnotatedProgramPoint(oldNode, 
				conjugatePredicates(oldNode.getPredicate(), predicate));
		AnnotatedProgramPoint newNode2 = new AnnotatedProgramPoint(oldNode, conjugatePredicates(
						oldNode.getPredicate(),	negatePredicateNoPU(predicate)));
		
		//connect predecessors of old node to new nodes, disconnect them from old node
		AppEdge[] oldInEdges = oldNode.getIncomingEdges().toArray(new AppEdge[]{});
		for (AppEdge oldInEdge : oldInEdges) {
			AnnotatedProgramPoint source = oldInEdge.getSource();
			CodeBlock statement = oldInEdge.getStatement();
			
			//deal with self loops elsewhere
			if (source.equals(oldNode))
				continue;
	
			if (oldInEdge instanceof AppHyperEdge) {
				AnnotatedProgramPoint hier = ((AppHyperEdge) oldInEdge).getHier();
				connectOutgoingReturnIfSat(source, hier, (Return) statement, newNode1);
				connectOutgoingReturnIfSat(source, hier, (Return) statement, newNode2);
			} else {
				connectOutgoingIfSat(source, statement, newNode1);
				connectOutgoingIfSat(source, statement, newNode2);
			}
			
			oldInEdge.disconnect();
		}
		
		//connect successors of old node to new nodes, disconnect them from old node
		AppEdge[] oldOutEdges = oldNode.getOutgoingEdges().toArray(new AppEdge[]{});
		for (AppEdge oldOutEdge : oldOutEdges) {
			AnnotatedProgramPoint target = oldOutEdge.getTarget();
			CodeBlock statement = oldOutEdge.getStatement();
			
			//deal with self loops elsewhere
			if (target.equals(oldNode))
				continue;
			
			if (oldOutEdge instanceof AppHyperEdge) {
				AnnotatedProgramPoint hier = ((AppHyperEdge) oldOutEdge).getHier();
				connectOutgoingReturnIfSat(newNode1, hier, (Return) statement, target);
				connectOutgoingReturnIfSat(newNode2, hier, (Return) statement, target);
			} else {
				connectOutgoingIfSat(newNode1, statement, target);
				connectOutgoingIfSat(newNode2, statement, target);
			}
			
			oldOutEdge.disconnect();
		}
		
		//deal with self loops
		for (AppEdge oldOutEdge : oldOutEdges) {
			AnnotatedProgramPoint target = oldOutEdge.getTarget();
			CodeBlock statement = oldOutEdge.getStatement();
			
			//already dealt with non self loops and disconnected those edges
			if (target == null)
				continue;		
			
			if (oldOutEdge instanceof AppHyperEdge) {
				AnnotatedProgramPoint hier = ((AppHyperEdge) oldOutEdge).getHier();
				connectOutgoingReturnIfSat(newNode1, hier, (Return) statement, newNode1);
				connectOutgoingReturnIfSat(newNode1, hier, (Return) statement, newNode2);
				connectOutgoingReturnIfSat(newNode2, hier, (Return) statement, newNode1);
				connectOutgoingReturnIfSat(newNode2, hier, (Return) statement, newNode2);
			} else {
				connectOutgoingIfSat(newNode1, statement, newNode1);
				connectOutgoingIfSat(newNode1, statement, newNode2);
				connectOutgoingIfSat(newNode2, statement, newNode1);
				connectOutgoingIfSat(newNode2, statement, newNode2);
			}
			
			oldOutEdge.disconnect();
		}
		
		//duplicate outgoing hyperedges
		AppHyperEdge[] oldOutHypEdges = oldNode.getOutgoingHyperEdges().toArray(new AppHyperEdge[]{});
		for (AppHyperEdge oldOutHypEdge : oldOutHypEdges) {
			AnnotatedProgramPoint source = oldOutHypEdge.getSource();
			AnnotatedProgramPoint target = oldOutHypEdge.getTarget();
			Return statement = (Return) oldOutHypEdge.getStatement();
			
			connectOutgoingReturnIfSat(source, newNode1, statement, target);
			connectOutgoingReturnIfSat(source, newNode2, statement, target);
			
			oldOutHypEdge.disconnect();
		}
	}
	
	private void splitNode_sdec(AnnotatedProgramPoint oldNode, IPredicate predicate) {
		//make two new nodes
		AnnotatedProgramPoint newNode1 = new AnnotatedProgramPoint(oldNode, 
				conjugatePredicates(oldNode.getPredicate(), predicate));
		AnnotatedProgramPoint newNode2 = new AnnotatedProgramPoint(oldNode, conjugatePredicates(
						oldNode.getPredicate(),	negatePredicateNoPU(predicate)));
		
		//connect predecessors of old node to new nodes, disconnect them from old node
		AppEdge[] oldInEdges = oldNode.getIncomingEdges().toArray(new AppEdge[]{});
		for (AppEdge oldInEdge : oldInEdges) {
			AnnotatedProgramPoint source = oldInEdge.getSource();
			CodeBlock statement = oldInEdge.getStatement();
			
			//deal with self loops elsewhere
			if (source.equals(oldNode))
				continue;
			if (statement instanceof DummyCodeBlock) {
				oldInEdge.disconnect();
				continue;
			}
			
			if (oldInEdge instanceof AppHyperEdge) {
				AnnotatedProgramPoint hier = ((AppHyperEdge) oldInEdge).getHier();
				if (_edgeChecker.sdecReturn(source.getPredicate(), 
						hier.getPredicate(), statement, 
						negatePredicateNoPU(newNode1.getPredicate())) == LBool.SAT)
					source.connectOutgoingReturn(hier, (Return) statement, newNode1);
				else
					connectOutgoingReturnIfSat(source, hier, (Return) statement, newNode1);	
				if (_edgeChecker.sdecReturn(source.getPredicate(), 
						hier.getPredicate(), statement, 
						negatePredicateNoPU(newNode2.getPredicate())) == LBool.SAT)
					source.connectOutgoingReturn(hier, (Return) statement, newNode2);
				else
					connectOutgoingReturnIfSat(source, hier, (Return) statement, newNode2);	
//				connectOutgoingReturnIfSat(source, hier, (Return) statement, newNode1);
//				connectOutgoingReturnIfSat(source, hier, (Return) statement, newNode2);
			} else {
				if (statement instanceof Call) {
					if (_edgeChecker.sdecCall(source.getPredicate(), statement, 
							negatePredicateNoPU(newNode1.getPredicate())) == LBool.SAT)
						source.connectOutgoing(statement, newNode1);
					else
						connectOutgoingIfSat(source, statement, newNode1);
					if (_edgeChecker.sdecCall(source.getPredicate(), statement, 
							negatePredicateNoPU(newNode2.getPredicate())) == LBool.SAT)
						source.connectOutgoing(statement, newNode2);
					else
						connectOutgoingIfSat(source, statement, newNode2);
				} else {
					if (_edgeChecker.sdecInteral(source.getPredicate(), statement, 
							negatePredicateNoPU(newNode1.getPredicate())) == LBool.SAT)
						source.connectOutgoing(statement, newNode1);
					else
						connectOutgoingIfSat(source, statement, newNode1);
					if (_edgeChecker.sdecInteral(source.getPredicate(), statement, 
							negatePredicateNoPU(newNode2.getPredicate())) == LBool.SAT)
						source.connectOutgoing(statement, newNode2);
					else
						connectOutgoingIfSat(source, statement, newNode2);	
				}
//				connectOutgoingIfSat(source, statement, newNode1);
//				connectOutgoingIfSat(source, statement, newNode2);
			}
			
			oldInEdge.disconnect();
		}
		
		//connect successors of old node to new nodes, disconnect them from old node
		AppEdge[] oldOutEdges = oldNode.getOutgoingEdges().toArray(new AppEdge[]{});
		for (AppEdge oldOutEdge : oldOutEdges) {
			AnnotatedProgramPoint target = oldOutEdge.getTarget();
			CodeBlock statement = oldOutEdge.getStatement();
			
			//deal with self loops elsewhere
			if (target.equals(oldNode))
				continue;
			
			if (oldOutEdge instanceof AppHyperEdge) {
				AnnotatedProgramPoint hier = ((AppHyperEdge) oldOutEdge).getHier();
				if (_edgeChecker.sdecReturn(newNode1.getPredicate(), hier.getPredicate(),
						statement, negatePredicateNoPU(target.getPredicate())) == LBool.SAT)
					newNode1.connectOutgoingReturn(hier, (Return) statement, target);
				else
					connectOutgoingReturnIfSat(newNode1, hier, (Return) statement, target);	
				if (_edgeChecker.sdecReturn(newNode2.getPredicate(), hier.getPredicate(),
						statement, negatePredicateNoPU(target.getPredicate())) == LBool.SAT)
					newNode2.connectOutgoingReturn(hier, (Return) statement, target);
				else
					connectOutgoingReturnIfSat(newNode2, hier, (Return) statement, target);	
//				connectOutgoingReturnIfSat(newNode1, hier, (Return) statement, target);
//				connectOutgoingReturnIfSat(newNode2, hier, (Return) statement, target);
			} else {
				if (statement instanceof Call) {
					if (_edgeChecker.sdecCall(newNode1.getPredicate(), statement, 
							negatePredicateNoPU(target.getPredicate())) == LBool.SAT)
						newNode1.connectOutgoing(statement, target);
					else
						connectOutgoingIfSat(newNode1, statement, target);
					if (_edgeChecker.sdecCall(newNode2.getPredicate(), statement, 
							negatePredicateNoPU(target.getPredicate())) == LBool.SAT)
						newNode2.connectOutgoing(statement, target);
					else
						connectOutgoingIfSat(newNode2, statement, target);
				} else {
					if (_edgeChecker.sdecInteral(newNode1.getPredicate(), statement, 
							negatePredicateNoPU(target.getPredicate())) == LBool.SAT)
						newNode1.connectOutgoing(statement, target);
					else
						connectOutgoingIfSat(newNode1, statement, target);
					if (_edgeChecker.sdecInteral(newNode2.getPredicate(), statement, 
							negatePredicateNoPU(target.getPredicate())) == LBool.SAT)
						newNode2.connectOutgoing(statement, target);
					else
						connectOutgoingIfSat(newNode2, statement, target);
				}
//				connectOutgoingIfSat(newNode1, statement, target);
//				connectoutgoingifsat(newnode2, statement, target);
			}
			
			oldOutEdge.disconnect();
		}
		
		//deal with self loops
		for (AppEdge oldOutEdge : oldOutEdges) {
			AnnotatedProgramPoint target = oldOutEdge.getTarget();
			CodeBlock statement = oldOutEdge.getStatement();
			
			//already dealt with non self loops and disconnected those edges
			if (target == null)
				continue;		
			
			if (oldOutEdge instanceof AppHyperEdge) {
				AnnotatedProgramPoint hier = ((AppHyperEdge) oldOutEdge).getHier();
//				if (_edgeChecker.sdecReturnSelfloopPre(newNode1.getPredicate(), (Return) statement) 
//						== LBool.SAT)
//					newNode1.connectOutgoingReturn(hier, (Return) statement, newNode1);
//				else
//					connectOutgoingReturnIfSat(newNode1, hier, (Return) statement, newNode1);	
//				if (_edgeChecker.sdecReturnSelfloopPre(newNode2.getPredicate(), (Return) statement) 
//						== LBool.SAT)
//					newNode2.connectOutgoingReturn(hier, (Return) statement, newNode2);
//				else
//					connectOutgoingReturnIfSat(newNode2, hier, (Return) statement, newNode2);	
				if (_edgeChecker.sdecReturn(newNode1.getPredicate(), hier.getPredicate(),
						statement, negatePredicateNoPU(newNode1.getPredicate())) == LBool.SAT)
					newNode1.connectOutgoingReturn(hier, (Return) statement, newNode1);
				else
					connectOutgoingReturnIfSat(newNode1, hier, (Return) statement, newNode1);	
				if (_edgeChecker.sdecReturn(newNode2.getPredicate(), hier.getPredicate(),
						statement, 
						negatePredicateNoPU(newNode2.getPredicate())) == LBool.SAT)
					newNode2.connectOutgoingReturn(hier, (Return) statement, newNode2);
				else
					connectOutgoingReturnIfSat(newNode2, hier, (Return) statement, newNode2);		
				
				if (_edgeChecker.sdecReturn(newNode1.getPredicate(), hier.getPredicate(),
						statement, negatePredicateNoPU(newNode2.getPredicate())) == LBool.SAT)
					newNode1.connectOutgoingReturn(hier, (Return) statement, newNode2);
				else
					connectOutgoingReturnIfSat(newNode1, hier, (Return) statement, newNode2);	
				if (_edgeChecker.sdecReturn(newNode2.getPredicate(), hier.getPredicate(),
						statement, 
						negatePredicateNoPU(newNode1.getPredicate())) == LBool.SAT)
					newNode2.connectOutgoingReturn(hier, (Return) statement, newNode1);
				else
					connectOutgoingReturnIfSat(newNode2, hier, (Return) statement, newNode1);		
//				connectOutgoingReturnIfSat(newNode1, hier, (Return) statement, newNode1);
//				connectOutgoingReturnIfSat(newNode1, hier, (Return) statement, newNode2);
//				connectOutgoingReturnIfSat(newNode2, hier, (Return) statement, newNode1);
//				connectOutgoingReturnIfSat(newNode2, hier, (Return) statement, newNode2);
			} else {
				if (statement instanceof Call) {
//					if (_edgeChecker.sdecCallSelfloop(newNode1.getPredicate(), statement)
//							== LBool.SAT)
//						newNode1.connectOutgoing(statement, newNode1);
//					else
//						connectOutgoingIfSat(newNode1, statement, newNode1);
//					if (_edgeChecker.sdecCallSelfloop(newNode2.getPredicate(), statement)
//							== LBool.SAT)
//						newNode2.connectOutgoing(statement, newNode2);
//					else
//						connectOutgoingIfSat(newNode2, statement, newNode2);
					if (_edgeChecker.sdecCall(newNode1.getPredicate(), statement, 
							negatePredicateNoPU(newNode1.getPredicate()))
							== LBool.SAT)
						newNode1.connectOutgoing(statement, newNode1);
					else
						connectOutgoingIfSat(newNode1, statement, newNode1);		
					if (_edgeChecker.sdecCall(newNode2.getPredicate(), statement, 
							negatePredicateNoPU(newNode2.getPredicate()))
							== LBool.SAT)
						newNode2.connectOutgoing(statement, newNode2);
					else
						connectOutgoingIfSat(newNode2, statement, newNode2);		
					
					if (_edgeChecker.sdecCall(newNode1.getPredicate(), statement, 
							negatePredicateNoPU(newNode2.getPredicate()))
							== LBool.SAT)
						newNode1.connectOutgoing(statement, newNode2);
					else
						connectOutgoingIfSat(newNode1, statement, newNode2);		
					if (_edgeChecker.sdecCall(newNode2.getPredicate(), statement, 
							negatePredicateNoPU(newNode1.getPredicate()))
							== LBool.SAT)
						newNode2.connectOutgoing(statement, newNode1);
					else
						connectOutgoingIfSat(newNode2, statement, newNode1);		
				} else {
//					if (_edgeChecker.sdecInternalSelfloop(newNode1.getPredicate(), statement)
//							== LBool.SAT)
//						newNode1.connectOutgoing(statement, newNode1);
//					else
//						connectOutgoingIfSat(newNode1, statement, newNode1);
//					if (_edgeChecker.sdecInternalSelfloop(newNode2.getPredicate(), statement)
//							== LBool.SAT)
//						newNode2.connectOutgoing(statement, newNode2);
//					else
//						connectOutgoingIfSat(newNode2, statement, newNode2);
					if (_edgeChecker.sdecInteral(newNode1.getPredicate(), statement, 
							negatePredicateNoPU(newNode1.getPredicate()))
							== LBool.SAT)
						newNode1.connectOutgoing(statement, newNode1);
					else
						connectOutgoingIfSat(newNode1, statement, newNode1);		
					if (_edgeChecker.sdecInteral(newNode2.getPredicate(), statement, 
							negatePredicateNoPU(newNode2.getPredicate()))
							== LBool.SAT)
						newNode2.connectOutgoing(statement, newNode2);
					else
						connectOutgoingIfSat(newNode2, statement, newNode2);		
					
					if (_edgeChecker.sdecInteral(newNode1.getPredicate(), statement, 
							negatePredicateNoPU(newNode2.getPredicate()))
							== LBool.SAT)
						newNode1.connectOutgoing(statement, newNode2);
					else
						connectOutgoingIfSat(newNode1, statement, newNode2);		
					if (_edgeChecker.sdecInteral(newNode2.getPredicate(), statement, 
							negatePredicateNoPU(newNode1.getPredicate()))
							== LBool.SAT)
						newNode2.connectOutgoing(statement, newNode1);
					else
						connectOutgoingIfSat(newNode2, statement, newNode1);		
				}
				
//				connectOutgoingIfSat(newNode1, statement, newNode1);
//				connectOutgoingIfSat(newNode1, statement, newNode2);
//				connectOutgoingIfSat(newNode2, statement, newNode1);
//				connectOutgoingIfSat(newNode2, statement, newNode2);
			}
			
			oldOutEdge.disconnect();
		}
		
		//duplicate outgoing hyperedges
		AppHyperEdge[] oldOutHypEdges = oldNode.getOutgoingHyperEdges().toArray(new AppHyperEdge[]{});
		for (AppHyperEdge oldOutHypEdge : oldOutHypEdges) {
			AnnotatedProgramPoint source = oldOutHypEdge.getSource();
			AnnotatedProgramPoint target = oldOutHypEdge.getTarget();
			Return statement = (Return) oldOutHypEdge.getStatement();
			
			if (_edgeChecker.sdecReturn(source.getPredicate(), 
					newNode1.getPredicate(), statement, negatePredicateNoPU(target.getPredicate())) == LBool.SAT)
				source.connectOutgoingReturn(newNode1, statement, target);
			else
				connectOutgoingReturnIfSat(source, newNode1, statement, target);	
			if (_edgeChecker.sdecReturn(source.getPredicate(), 
					newNode2.getPredicate(), statement, negatePredicateNoPU(target.getPredicate())) == LBool.SAT)
				source.connectOutgoingReturn(newNode2, statement, target);
			else
				connectOutgoingReturnIfSat(source, newNode2, statement, target);	
//			connectOutgoingReturnIfSat(source, newNode1, statement, target);
//			connectOutgoingReturnIfSat(source, newNode2, statement, target);
			
			oldOutHypEdge.disconnect();
		}
	}
	
	/**
	 * Given a node and a corresponding interpolants, then split the node with
	 * annotating the interpolants according to the algorithm of ULtimate model
	 * checker. The nodes generated from split are added to the hashMap
	 * nodesClones.
	 * 
	 * @param oldNode
	 * @param interpolant
	 * @return
	 */
	private void splitNode_EdgeChecker(AnnotatedProgramPoint oldNode, IPredicate predicate) {
		//make two new nodes
		AnnotatedProgramPoint newNode1 = new AnnotatedProgramPoint(oldNode, 
				conjugatePredicates(oldNode.getPredicate(), predicate));
		AnnotatedProgramPoint newNode2 = new AnnotatedProgramPoint(oldNode, conjugatePredicates(
						oldNode.getPredicate(),	negatePredicateNoPU(predicate)));
		
		AnnotatedProgramPoint[] newNodes = new AnnotatedProgramPoint[] { newNode1, newNode2 };
		
		//connect predecessors of old node to new nodes, disconnect them from old node
		AppEdge[] oldInEdges = oldNode.getIncomingEdges().toArray(new AppEdge[]{});
		for (AppEdge oldInEdge : oldInEdges) {
			AnnotatedProgramPoint source = oldInEdge.getSource();
			CodeBlock statement = oldInEdge.getStatement();
			//deal with self loops elsewhere
			if (source.equals(oldNode))
				continue;	
			if (statement instanceof DummyCodeBlock) {
				oldInEdge.disconnect();
				continue;
			}
			
			_edgeChecker.assertCodeBlock(statement);
			_edgeChecker.assertPrecondition(source.getPredicate());
			
			if (oldInEdge instanceof AppHyperEdge) {
				AnnotatedProgramPoint hier = ((AppHyperEdge) oldInEdge).getHier();
				_edgeChecker.assertHierPred(hier.getPredicate());
				if (_edgeChecker.postReturnImplies(negatePredicateNoPU(newNode1.getPredicate())) != LBool.UNSAT)
						source.connectOutgoingReturn(hier, (Return) statement, newNode1);	
				if (_edgeChecker.postReturnImplies(negatePredicateNoPU(newNode2.getPredicate())) != LBool.UNSAT)
						source.connectOutgoingReturn(hier, (Return) statement, newNode2);
//				connectOutgoingReturnIfSat(source, hier, (Return) statement, newNode1);
//				connectOutgoingReturnIfSat(source, hier, (Return) statement, newNode2);
				_edgeChecker.unAssertHierPred();
			} else {
				if (statement instanceof Call) {
					if (_edgeChecker.postCallImplies(negatePredicateNoPU(newNode1.getPredicate())) != LBool.UNSAT)
						source.connectOutgoing(statement, newNode1);
					if (_edgeChecker.postCallImplies(negatePredicateNoPU(newNode2.getPredicate())) != LBool.UNSAT)
						source.connectOutgoing(statement, newNode2);
				} else {
					if (_edgeChecker.postInternalImplies(negatePredicateNoPU(newNode1.getPredicate())) != LBool.UNSAT)
						source.connectOutgoing(statement, newNode1);
					if (_edgeChecker.postInternalImplies(negatePredicateNoPU(newNode2.getPredicate())) != LBool.UNSAT)
						source.connectOutgoing(statement, newNode2);	
				}
//				connectOutgoingIfSat(source, statement, newNode1);
//				connectOutgoingIfSat(source, statement, newNode2);
			}
	
//			if (oldInEdge instanceof AppHyperEdge) {
//				AnnotatedProgramPoint hier = ((AppHyperEdge) oldInEdge).getHier();
//				connectOutgoingReturnIfSat(source, hier, (Return) statement, newNode1);
//				connectOutgoingReturnIfSat(source, hier, (Return) statement, newNode2);
//			} else {
//				connectOutgoingIfSat(source, statement, newNode1);
//				connectOutgoingIfSat(source, statement, newNode2);
//			}
			
			oldInEdge.disconnect();
			_edgeChecker.unAssertPrecondition();
			_edgeChecker.unAssertCodeBlock();
		}
		
		
		
		//connect successors of old node to new nodes, disconnect them from old node
		AppEdge[] oldOutEdges = oldNode.getOutgoingEdges().toArray(new AppEdge[]{});
		for (int i = 0; i < 2; i++) {
//			_edgeChecker.assertPrecondition(newNodes[i].getPredicate());
			for (AppEdge oldOutEdge : oldOutEdges) {
				AnnotatedProgramPoint target = oldOutEdge.getTarget();
				CodeBlock statement = oldOutEdge.getStatement();

				//deal with self loops elsewhere
				if (target.equals(oldNode))
					continue;
				_edgeChecker.assertCodeBlock(statement);
				_edgeChecker.assertPrecondition(newNodes[i].getPredicate());

				if (oldOutEdge instanceof AppHyperEdge) {
					AnnotatedProgramPoint hier = ((AppHyperEdge) oldOutEdge).getHier();
					_edgeChecker.assertHierPred(hier.getPredicate());
					if (_edgeChecker.postReturnImplies(negatePredicateNoPU(target.getPredicate())) != LBool.UNSAT)
						newNodes[i].connectOutgoingReturn(hier, (Return) statement, target);	
					//				connectOutgoingReturnIfSat(newNode2, hier, (Return) statement, target);
					_edgeChecker.unAssertHierPred();
				} else {
					if (statement instanceof Call) {
						if (_edgeChecker.postCallImplies(negatePredicateNoPU(target.getPredicate())) != LBool.UNSAT)
							newNodes[i].connectOutgoing(statement, target);
					} else {
						if (_edgeChecker.postInternalImplies(negatePredicateNoPU(target.getPredicate())) != LBool.UNSAT)
							newNodes[i].connectOutgoing(statement, target);
					}
					//				connectOutgoingIfSat(newNode2, statement, target);
				}

				if (i == 1)
					oldOutEdge.disconnect();
				_edgeChecker.unAssertCodeBlock();		
				_edgeChecker.unAssertPrecondition();

				//			if (oldOutEdge instanceof AppHyperEdge) {
				//				AnnotatedProgramPoint hier = ((AppHyperEdge) oldOutEdge).getHier();
				//				connectOutgoingReturnIfSat(newNode1, hier, (Return) statement, target);
				//			} else {
				//				connectOutgoingIfSat(newNode1, statement, target);
				//			}
			}
//			_edgeChecker.unAssertPrecondition();
		}

		
		//deal with self loops
		for (int i = 0; i < 2; i++) {
//			_edgeChecker.assertPrecondition(newNodes[i].getPredicate());
			for (AppEdge oldOutEdge : oldOutEdges) {
				AnnotatedProgramPoint target = oldOutEdge.getTarget();
				CodeBlock statement = oldOutEdge.getStatement();
				//already dealt with non self loops and disconnected those edges
				if (target == null)
					continue;		
				
				_edgeChecker.assertCodeBlock(statement);
				_edgeChecker.assertPrecondition(newNodes[i].getPredicate());

				if (oldOutEdge instanceof AppHyperEdge) {
					AnnotatedProgramPoint hier = ((AppHyperEdge) oldOutEdge).getHier();
					_edgeChecker.assertHierPred(hier.getPredicate());
					if (_edgeChecker.postReturnImplies(negatePredicateNoPU(newNode1.getPredicate())) != LBool.UNSAT)
						newNodes[i].connectOutgoingReturn(hier, (Return) statement, newNode1);
					if (_edgeChecker.postReturnImplies(negatePredicateNoPU(newNode2.getPredicate())) != LBool.UNSAT)
						newNodes[i].connectOutgoingReturn(hier, (Return) statement, newNode2);
					_edgeChecker.unAssertHierPred();
//					connectOutgoingReturnIfSat(newNode1, hier, (Return) statement, newNode1);
//					connectOutgoingReturnIfSat(newNode1, hier, (Return) statement, newNode2);
//					connectOutgoingReturnIfSat(newNode2, hier, (Return) statement, newNode1);
//					connectOutgoingReturnIfSat(newNode2, hier, (Return) statement, newNode2);
				} else {
					if (statement instanceof Call) {
						if  (_edgeChecker.postCallImplies(negatePredicateNoPU(newNode1.getPredicate())) != LBool.UNSAT)
							newNodes[i].connectOutgoing(statement, newNode1);
						if  (_edgeChecker.postCallImplies(negatePredicateNoPU(newNode2.getPredicate())) != LBool.UNSAT)
							newNodes[i].connectOutgoing(statement, newNode2);
					} else {
						if  (_edgeChecker.postInternalImplies(negatePredicateNoPU(newNode1.getPredicate())) != LBool.UNSAT)
							newNodes[i].connectOutgoing(statement, newNode1);
						if  (_edgeChecker.postInternalImplies(negatePredicateNoPU(newNode2.getPredicate())) != LBool.UNSAT)
							newNodes[i].connectOutgoing(statement, newNode2);
					}
//					connectOutgoingIfSat(newNode1, statement, newNode1);
//					connectOutgoingIfSat(newNode1, statement, newNode2);
//					connectOutgoingIfSat(newNode2, statement, newNode1);
//					connectOutgoingIfSat(newNode2, statement, newNode2);
				}
				_edgeChecker.unAssertCodeBlock();
				_edgeChecker.unAssertPrecondition();
				if (i == 1)
					oldOutEdge.disconnect();
			}
//			_edgeChecker.unAssertPrecondition();
		}
		
		//duplicate outgoing hyperedges
		AppHyperEdge[] oldOutHypEdges = oldNode.getOutgoingHyperEdges().toArray(new AppHyperEdge[]{});
		for (AppHyperEdge oldOutHypEdge : oldOutHypEdges) {
			AnnotatedProgramPoint source = oldOutHypEdge.getSource();
			AnnotatedProgramPoint target = oldOutHypEdge.getTarget();
			Return statement = (Return) oldOutHypEdge.getStatement();
			
			_edgeChecker.assertCodeBlock(statement);
			_edgeChecker.assertPrecondition(source.getPredicate());
			
			for (int i = 0; i < 2; i++) {
				_edgeChecker.assertHierPred(newNodes[i].getPredicate());
				if (_edgeChecker.postReturnImplies(negatePredicateNoPU(target.getPredicate())) != LBool.UNSAT)
					source.connectOutgoingReturn(newNodes[i], statement, target);
				_edgeChecker.unAssertHierPred();
			}
//			connectOutgoingReturnIfSat(source, newNode1, statement, target);
//			connectOutgoingReturnIfSat(source, newNode2, statement, target);
			
			oldOutHypEdge.disconnect();
			_edgeChecker.unAssertPrecondition();
			_edgeChecker.unAssertCodeBlock();
		}
	}
	
	/**
	 * Given an error trace with the corresponding interpolants, then it
	 * modifies the graph accordingly.
	 */
	public boolean codeCheck(
			NestedRun<CodeBlock, AnnotatedProgramPoint> errorRun,
			IPredicate[] interpolants, AnnotatedProgramPoint procedureRoot) {

		// Debug The Error Trace and the corresponding list of interpolants.
		AnnotatedProgramPoint[] nodes = errorRun.getStateSequence().toArray(
				new AnnotatedProgramPoint[0]);
		ArrayList<AnnotatedProgramPoint> errorTraceDBG = new ArrayList<AnnotatedProgramPoint>();
		Collections.addAll(errorTraceDBG, nodes);
		CodeCheckObserver.s_Logger.debug(String.format("Error: %s\n",
				errorTraceDBG));

		ArrayList<IPredicate> interpolantsDBG = new ArrayList<IPredicate>();
		Collections.addAll(interpolantsDBG, interpolants);
		CodeCheckObserver.s_Logger.debug(String.format("Inters: %s\n",
				interpolantsDBG));
		
		

		int splitMode = 0;
		for (int i = 0; i < interpolants.length; i++) {
//			_pre2stm2post_toConnectIfSat = 
//					new HashMap<AnnotatedProgramPoint, 
//					HashMap<CodeBlock,AnnotatedProgramPoint>>();
//			_pre2hier2stm2post_toConnectIfSat = 
//					new HashMap<AnnotatedProgramPoint, 
//					HashMap<AnnotatedProgramPoint,
//					HashMap<Return,AnnotatedProgramPoint>>>();
			switch (splitMode) {
			case 0:
				splitNode_Normal(nodes[i + 1], interpolants[i]);
				break;
			case 1:
				splitNode_sdec(nodes[i + 1], interpolants[i]);
				break;
			case 2:
				splitNode_EdgeChecker(nodes[i + 1], interpolants[i]);
				break;
			}
//			makeConnections();
		} 
		
		return true;
	}
	
	@Override
	public boolean codeCheck(
			NestedRun<CodeBlock, AnnotatedProgramPoint> errorRun,
			IPredicate[] interpolants,
			AnnotatedProgramPoint procedureRoot,
			HashMap<IPredicate, HashMap<CodeBlock, HashSet<IPredicate>>> satTriples,
			HashMap<IPredicate, HashMap<CodeBlock, HashSet<IPredicate>>> unsatTriples) {
		this._memoizeNormalEdgeChecks = true;
		this._satTriples = satTriples;
		this._unsatTriples = unsatTriples;
		return this.codeCheck(errorRun, interpolants, procedureRoot);
	}

	private void makeConnections() {
		for (Entry<AnnotatedProgramPoint, HashMap<CodeBlock, AnnotatedProgramPoint>> pre2  
				: _pre2stm2post_toConnectIfSat.entrySet()) 
			for (Entry<CodeBlock, AnnotatedProgramPoint> stm2 
					: pre2.getValue().entrySet()) 
				if (isSatEdge(pre2.getKey().getPredicate(), stm2.getKey(), stm2.getValue().getPredicate())) 
					pre2.getKey().connectOutgoing(stm2.getKey(), stm2.getValue());
		
		for (Entry<AnnotatedProgramPoint, HashMap<AnnotatedProgramPoint, HashMap<Return, AnnotatedProgramPoint>>> pre2
				: _pre2hier2stm2post_toConnectIfSat.entrySet())
			for (Entry<AnnotatedProgramPoint, HashMap<Return, AnnotatedProgramPoint>> hier2  
					: pre2.getValue().entrySet()) 
				for (Entry<Return, AnnotatedProgramPoint> stm2 
						: hier2.getValue().entrySet()) 
					if (isSatRetEdge(pre2.getKey(), hier2.getKey(), stm2.getKey(), stm2.getValue())) 
						pre2.getKey().connectOutgoingReturn(hier2.getKey(), stm2.getKey(), stm2.getValue());	
	}

	/**
	 * Check if an edge between two AnnotatedProgramPoints is satisfiable or not, works with
	 * the cases if the edge is a normal edge or a call edge.
	 * @param preCondition
	 * @param statement
	 * @param postCondition
	 * @return
	 */
	protected boolean isSatEdge(IPredicate preCondition, CodeBlock statement,
			IPredicate postCondition) {
		if (statement instanceof DummyCodeBlock)
			return false;
//		System.out.print(".");
		
		if (_memoizeNormalEdgeChecks) {
			if (_satTriples.get(preCondition) != null
					&& _satTriples.get(preCondition).get(statement) != null
					&& _satTriples.get(preCondition).get(statement).contains(postCondition)) {
				memoizationHitsSat++;
				return true;
			}
			if (_unsatTriples.get(preCondition) != null
					&& _unsatTriples.get(preCondition).get(statement) != null
					&& _unsatTriples.get(preCondition).get(statement).contains(postCondition)) {
				memoizationHitsUnsat++;
				return false;
			}
		}
		
		boolean result = false;
		if (statement instanceof Call) 
			result = m_smtManager.isInductiveCall(preCondition, 
					(Call) statement, negatePredicateNoPU(postCondition)) != LBool.UNSAT;
		else
			result = m_smtManager.isInductive(preCondition, statement, 
					negatePredicateNoPU(postCondition)) != LBool.UNSAT;
		
		if (_memoizeNormalEdgeChecks)
			if (result)
				addSatTriple(preCondition, statement, postCondition);
			else 
				addUnsatTriple(preCondition, statement, postCondition);
		
		return result;
	}
	
	/**
	 * Check if a return edge between two AnnotatedProgramPoints is satisfiable or not.
	 * @param sourceNode
	 * @param edgeLabel
	 * @param destinationNode
	 * @param callNode
	 * @return
	 */
	protected boolean isSatRetEdge(AnnotatedProgramPoint sourceNode, AnnotatedProgramPoint callNode, Return edgeLabel,
			AnnotatedProgramPoint destinationNode) {
//		System.out.print(".");
		return m_smtManager.isInductiveReturn(sourceNode.getPredicate(), 
				callNode.getPredicate(), 
				(Return) edgeLabel, 
				negatePredicateNoPU(destinationNode.getPredicate())) != LBool.UNSAT;
	}
	
	protected void connectOutgoingIfSat(AnnotatedProgramPoint source,
			CodeBlock statement, AnnotatedProgramPoint target) {
//		if (_pre2stm2post_toConnectIfSat.get(source) == null)
//			_pre2stm2post_toConnectIfSat.put(source, new HashMap<CodeBlock, AnnotatedProgramPoint>());
//		_pre2stm2post_toConnectIfSat.get(source).put(statement, target);
		
		if (isSatEdge(source.getPredicate(), statement, target.getPredicate()))
			source.connectOutgoing(statement, target);
	}

	protected void connectOutgoingReturnIfSat(AnnotatedProgramPoint source,
			AnnotatedProgramPoint hier, Return statement,
			AnnotatedProgramPoint target) {
//		if (_pre2hier2stm2post_toConnectIfSat.get(source) == null)
//			_pre2hier2stm2post_toConnectIfSat.put(source, new HashMap<AnnotatedProgramPoint, HashMap<Return,AnnotatedProgramPoint>>());
//		if (_pre2hier2stm2post_toConnectIfSat.get(source).get(hier) == null)
//			_pre2hier2stm2post_toConnectIfSat.get(source).put(hier, new HashMap<Return, AnnotatedProgramPoint>());
//		_pre2hier2stm2post_toConnectIfSat.get(source).get(hier).put(statement, target);
		
		if (isSatRetEdge(source, hier, statement, target))
			source.connectOutgoingReturn(hier, statement, target);
	}	
	
	void addSatTriple(IPredicate pre, CodeBlock stm, IPredicate post) {
		if (_satTriples.get(pre) == null)
			_satTriples.put(pre, new HashMap<CodeBlock, HashSet<IPredicate>>());
		if (_satTriples.get(pre).get(stm) == null)
			_satTriples.get(pre).put(stm, new HashSet<IPredicate>());
		_satTriples.get(pre).get(stm).add(post);
	}
	
	void addUnsatTriple(IPredicate pre, CodeBlock stm, IPredicate post) {
		if (_unsatTriples.get(pre) == null)
			_unsatTriples.put(pre, new HashMap<CodeBlock, HashSet<IPredicate>>());
		if (_unsatTriples.get(pre).get(stm) == null)
			_unsatTriples.get(pre).put(stm, new HashSet<IPredicate>());
		_unsatTriples.get(pre).get(stm).add(post);
	}
}
