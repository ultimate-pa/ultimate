package de.uni_freiburg.informatik.ultimate.plugins.generator.kojak;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map.Entry;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedRun;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.TransFormula.Infeasibility;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.appgraph.AnnotatedProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.appgraph.AppEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.appgraph.AppHyperEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.appgraph.DummyCodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.appgraph.ImpRootNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck.CodeChecker;
import de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck.GlobalSettings;
import de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck.GraphWriter;
import de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck.preferences.CodeCheckPreferenceInitializer.EdgeCheckOptimization;
import de.uni_freiburg.informatik.ultimate.plugins.generator.codecheck.preferences.CodeCheckPreferenceInitializer.PredicateUnification;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.EdgeChecker;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.IHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.IHoareTripleChecker.Validity;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.PredicateUnifier;
import de.uni_freiburg.informatik.ultimate.util.relation.IsContained;
import de.uni_freiburg.informatik.ultimate.util.relation.NestedMap3;
import de.uni_freiburg.informatik.ultimate.util.relation.NestedMap4;

/**
 * UltimateChecker class, implements the model checker Ultimate.
 * 
 * @author Mostafa Mahmoud
 * 
 */
public class UltimateChecker extends CodeChecker {

	HashMap<AnnotatedProgramPoint, HashMap<CodeBlock, AnnotatedProgramPoint>> _pre2stm2post_toConnectIfSat;
	HashMap<AnnotatedProgramPoint, HashMap<AnnotatedProgramPoint, HashMap<Return, AnnotatedProgramPoint>>> _pre2hier2stm2post_toConnectIfSat;

	public UltimateChecker(IElement root, SmtManager m_smtManager, TAPreferences m_taPrefs, RootNode m_originalRoot, ImpRootNode m_graphRoot,
			GraphWriter m_graphWriter, IHoareTripleChecker edgeChecker, PredicateUnifier predicateUnifier, Logger logger) {
		super(root, m_smtManager, m_taPrefs, m_originalRoot, m_graphRoot,
				m_graphWriter, edgeChecker, predicateUnifier, logger);
	}

	/**
	 * Given an error trace with the corresponding interpolants, then it
	 * modifies the graph accordingly.
	 */
	public boolean codeCheck(NestedRun<CodeBlock, AnnotatedProgramPoint> errorRun, IPredicate[] interpolants,
			AnnotatedProgramPoint procedureRoot) {

		// Debug The Error Trace and the corresponding list of interpolants.
		AnnotatedProgramPoint[] nodes = errorRun.getStateSequence().toArray(new AnnotatedProgramPoint[0]);
		ArrayList<AnnotatedProgramPoint> errorTraceDBG = new ArrayList<AnnotatedProgramPoint>();
		Collections.addAll(errorTraceDBG, nodes);
		mLogger.debug(String.format("Error: %s\n", errorTraceDBG));

		ArrayList<IPredicate> interpolantsDBG = new ArrayList<IPredicate>();
		Collections.addAll(interpolantsDBG, interpolants);
		mLogger.debug(String.format("Inters: %s\n", interpolantsDBG));
		System.err.println(String.format("Inters: %s\n", interpolantsDBG));

		for (int i = 0; i < interpolants.length; i++) {
			splitNode(nodes[i + 1], interpolants[i]);

		}

		return true;
	}

	private void splitNode(AnnotatedProgramPoint oldNode,
			IPredicate predicate) {
		// make two new nodes
		AnnotatedProgramPoint newNode1 = new AnnotatedProgramPoint(oldNode, conjugatePredicates(oldNode.getPredicate(),
				predicate));
		AnnotatedProgramPoint newNode2 = new AnnotatedProgramPoint(oldNode, conjugatePredicates(oldNode.getPredicate(),
				negatePredicateNoPU(predicate)));

		// connect predecessors of old node to new nodes, disconnect them from
		// old node
		AppEdge[] oldInEdges = oldNode.getIncomingEdges().toArray(new AppEdge[] {});
		for (AppEdge oldInEdge : oldInEdges) {
			AnnotatedProgramPoint source = oldInEdge.getSource();
			CodeBlock statement = oldInEdge.getStatement();

			// deal with self loops elsewhere
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

		// connect successors of old node to new nodes, disconnect them from old
		// node
		AppEdge[] oldOutEdges = oldNode.getOutgoingEdges().toArray(new AppEdge[] {});
		for (AppEdge oldOutEdge : oldOutEdges) {
			AnnotatedProgramPoint target = oldOutEdge.getTarget();
			CodeBlock statement = oldOutEdge.getStatement();

			// deal with self loops elsewhere
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

		// deal with self loops
		for (AppEdge oldOutEdge : oldOutEdges) {
			AnnotatedProgramPoint target = oldOutEdge.getTarget();
			CodeBlock statement = oldOutEdge.getStatement();

			// already dealt with non self loops and disconnected those edges
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

		// duplicate outgoing hyperedges
		AppHyperEdge[] oldOutHypEdges = oldNode.getOutgoingHyperEdges().toArray(new AppHyperEdge[] {});
		for (AppHyperEdge oldOutHypEdge : oldOutHypEdges) {
			AnnotatedProgramPoint source = oldOutHypEdge.getSource();
			AnnotatedProgramPoint target = oldOutHypEdge.getTarget();
			Return statement = (Return) oldOutHypEdge.getStatement();

			connectOutgoingReturnIfSat(source, newNode1, statement, target);
			connectOutgoingReturnIfSat(source, newNode2, statement, target);

			oldOutHypEdge.disconnect();
		}
	}

	@Override
	public boolean codeCheck(NestedRun<CodeBlock, AnnotatedProgramPoint> errorRun, IPredicate[] interpolants,
			AnnotatedProgramPoint procedureRoot,
			NestedMap3<IPredicate, CodeBlock, IPredicate, IsContained> satTriples,
			NestedMap3<IPredicate, CodeBlock, IPredicate, IsContained> unsatTriples) {
		this._satTriples = satTriples;
		this._unsatTriples = unsatTriples;
		return this.codeCheck(errorRun, interpolants, procedureRoot);
	}

	@Override
	public boolean codeCheck(NestedRun<CodeBlock, AnnotatedProgramPoint> errorRun, IPredicate[] interpolants,
			AnnotatedProgramPoint procedureRoot,
			NestedMap3<IPredicate, CodeBlock, IPredicate, IsContained> satTriples,
			NestedMap3<IPredicate, CodeBlock, IPredicate, IsContained> unsatTriples,
			NestedMap4<IPredicate, IPredicate, CodeBlock, IPredicate, IsContained> satQuadruples,
			NestedMap4<IPredicate, IPredicate, CodeBlock, IPredicate, IsContained> unsatQuadruples) {
		this._satQuadruples = satQuadruples;
		this._unsatQuadruples = unsatQuadruples;
		return this.codeCheck(errorRun, interpolants, procedureRoot, satTriples, unsatTriples);
	}

	private void makeConnections() {
		for (Entry<AnnotatedProgramPoint, HashMap<CodeBlock, AnnotatedProgramPoint>> pre2 : _pre2stm2post_toConnectIfSat
				.entrySet())
			for (Entry<CodeBlock, AnnotatedProgramPoint> stm2 : pre2.getValue().entrySet())
				if (isSatEdge(pre2.getKey().getPredicate(), stm2.getKey(), stm2.getValue().getPredicate()))
					pre2.getKey().connectOutgoing(stm2.getKey(), stm2.getValue());

		for (Entry<AnnotatedProgramPoint, HashMap<AnnotatedProgramPoint, HashMap<Return, AnnotatedProgramPoint>>> pre2 : _pre2hier2stm2post_toConnectIfSat
				.entrySet())
			for (Entry<AnnotatedProgramPoint, HashMap<Return, AnnotatedProgramPoint>> hier2 : pre2.getValue()
					.entrySet())
				for (Entry<Return, AnnotatedProgramPoint> stm2 : hier2.getValue().entrySet())
					if (isSatRetEdge(pre2.getKey().getPredicate(), hier2.getKey().getPredicate(), stm2.getKey(), stm2
							.getValue().getPredicate()))
						pre2.getKey().connectOutgoingReturn(hier2.getKey(), stm2.getKey(), stm2.getValue());
	}

	protected boolean connectOutgoingIfSat(AnnotatedProgramPoint source, CodeBlock statement, AnnotatedProgramPoint target) {
		if (isSatEdge(source.getPredicate(), statement, target.getPredicate())) {
			source.connectOutgoing(statement, target);
			return true;
		} else {
			return false;
		}
	}

	protected boolean connectOutgoingReturnIfSat(AnnotatedProgramPoint source, AnnotatedProgramPoint hier,
			Return statement, AnnotatedProgramPoint target) {
		if (isSatRetEdge(source.getPredicate(), hier.getPredicate(), statement, target.getPredicate())) {
			source.connectOutgoingReturn(hier, statement, target);
			return true;
		} else {
			return false;
		}
	}
	

	/**
	 * Check if an edge between two AnnotatedProgramPoints is satisfiable or
	 * not, works with the cases if the edge is a normal edge or a call edge.
	 * 
	 * @param preCondition
	 * @param statement
	 * @param postCondition
	 * @return
	 */
	protected boolean isSatEdge(IPredicate preCondition, CodeBlock statement, IPredicate postCondition) {
		if (statement instanceof DummyCodeBlock)
			return false;

		if (GlobalSettings._instance._memoizeNormalEdgeChecks) {
			if (_satTriples.get(preCondition, statement, postCondition) == IsContained.IsContained) {
				memoizationHitsSat++;
				return true;
			}
			if (_unsatTriples.get(preCondition, statement, postCondition) == IsContained.IsContained) {
				memoizationHitsUnsat++;
				return false;
			}
		}

		boolean result = false;
		if (statement instanceof Call)
			//result is true if pre /\ stm /\ post is sat or unknown, false if unsat 
			result = _edgeChecker.checkCall(preCondition, statement, negatePredicateNoPU(postCondition)) != Validity.VALID;
		else
			result = _edgeChecker.checkInternal(preCondition, statement, negatePredicateNoPU(postCondition)) != Validity.VALID;

		if (GlobalSettings._instance._memoizeNormalEdgeChecks)
			if (result)
				_satTriples.put(preCondition, statement, postCondition, IsContained.IsContained);
			else
				_unsatTriples.put(preCondition, statement, postCondition, IsContained.IsContained);

		return result;
	}

	/**
	 * Check if a return edge between two AnnotatedProgramPoints is satisfiable
	 * or not.
	 * 
	 * @param preCondition
	 * @param statement
	 * @param destinationNode
	 * @param hier
	 * @return
	 */
	protected boolean isSatRetEdge(IPredicate preCondition, IPredicate hier, Return statement, IPredicate postCondition) {
		if (GlobalSettings._instance._memoizeReturnEdgeChecks) {
			if (_satQuadruples.get(preCondition, hier, statement, postCondition) == IsContained.IsContained) {
				memoizationReturnHitsSat++;
				return true;
			}
			if (_unsatQuadruples.get(preCondition, hier, statement, postCondition) == IsContained.IsContained) {
				memoizationReturnHitsUnsat++;
				return false;
			}
		}

		boolean result = _edgeChecker.checkReturn(preCondition, hier, (Return) statement,
				negatePredicateNoPU(postCondition)) != Validity.VALID;

		if (GlobalSettings._instance._memoizeReturnEdgeChecks)
			if (result)
				_satQuadruples.put(preCondition, hier, statement, postCondition, IsContained.IsContained);
			else
				_unsatQuadruples.put(preCondition, hier, statement, postCondition, IsContained.IsContained);

		return result;
	}

}
