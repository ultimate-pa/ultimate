/*
 * Copyright (C) 2014-2015 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
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
package de.uni_freiburg.informatik.ultimate.plugins.generator.kojak;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedRun;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.ICallAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IInternalAction;
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
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.PredicateUnifier;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.IsContained;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap3;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap4;

/**
 * UltimateChecker class, implements the model checker Ultimate.
 * 
 * @author Mostafa Mahmoud
 * 
 */
public class UltimateChecker extends CodeChecker {

	HashMap<AnnotatedProgramPoint, HashMap<CodeBlock, AnnotatedProgramPoint>> _pre2stm2post_toConnectIfSat;
	HashMap<AnnotatedProgramPoint, HashMap<AnnotatedProgramPoint, HashMap<Return, AnnotatedProgramPoint>>> _pre2hier2stm2post_toConnectIfSat;

	public UltimateChecker(IElement root, SmtManager msmtManager, RootNode moriginalRoot, ImpRootNode mgraphRoot,
			GraphWriter mgraphWriter, IHoareTripleChecker edgeChecker, PredicateUnifier predicateUnifier, ILogger logger) {
		super(root, msmtManager, moriginalRoot, mgraphRoot,
				mgraphWriter, edgeChecker, predicateUnifier, logger);
	}

	/**
	 * Given an error trace with the corresponding interpolants, then it
	 * modifies the graph accordingly.
	 */
	@Override
	public boolean codeCheck(NestedRun<CodeBlock, AnnotatedProgramPoint> errorRun, IPredicate[] interpolants,
			AnnotatedProgramPoint procedureRoot) {

		// Debug The Error Trace and the corresponding list of interpolants.
		final AnnotatedProgramPoint[] nodes = errorRun.getStateSequence().toArray(new AnnotatedProgramPoint[0]);
		final ArrayList<AnnotatedProgramPoint> errorTraceDBG = new ArrayList<AnnotatedProgramPoint>();
		Collections.addAll(errorTraceDBG, nodes);
		mLogger.debug(String.format("Error: %s\n", errorTraceDBG));

		final ArrayList<IPredicate> interpolantsDBG = new ArrayList<IPredicate>();
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
		final AnnotatedProgramPoint newNode1 = new AnnotatedProgramPoint(oldNode, conjugatePredicates(oldNode.getPredicate(),
				predicate));
		final AnnotatedProgramPoint newNode2 = new AnnotatedProgramPoint(oldNode, conjugatePredicates(oldNode.getPredicate(),
				negatePredicateNoPU(predicate)));

		// connect predecessors of old node to new nodes, disconnect them from
		// old node
		final AppEdge[] oldInEdges = oldNode.getIncomingEdges().toArray(new AppEdge[] {});
		for (final AppEdge oldInEdge : oldInEdges) {
			final AnnotatedProgramPoint source = oldInEdge.getSource();
			final CodeBlock statement = oldInEdge.getStatement();

			// deal with self loops elsewhere
			if (source.equals(oldNode)) {
				continue;
			}

			if (oldInEdge instanceof AppHyperEdge) {
				final AnnotatedProgramPoint hier = ((AppHyperEdge) oldInEdge).getHier();
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
		final AppEdge[] oldOutEdges = oldNode.getOutgoingEdges().toArray(new AppEdge[] {});
		for (final AppEdge oldOutEdge : oldOutEdges) {
			final AnnotatedProgramPoint target = oldOutEdge.getTarget();
			final CodeBlock statement = oldOutEdge.getStatement();

			// deal with self loops elsewhere
			if (target.equals(oldNode)) {
				continue;
			}

			if (oldOutEdge instanceof AppHyperEdge) {
				final AnnotatedProgramPoint hier = ((AppHyperEdge) oldOutEdge).getHier();
				connectOutgoingReturnIfSat(newNode1, hier, (Return) statement, target);
				connectOutgoingReturnIfSat(newNode2, hier, (Return) statement, target);
			} else {
				connectOutgoingIfSat(newNode1, statement, target);
				connectOutgoingIfSat(newNode2, statement, target);
			}

			oldOutEdge.disconnect();
		}

		// deal with self loops
		for (final AppEdge oldOutEdge : oldOutEdges) {
			final AnnotatedProgramPoint target = oldOutEdge.getTarget();
			final CodeBlock statement = oldOutEdge.getStatement();

			// already dealt with non self loops and disconnected those edges
			if (target == null) {
				continue;
			}

			if (oldOutEdge instanceof AppHyperEdge) {
				final AnnotatedProgramPoint hier = ((AppHyperEdge) oldOutEdge).getHier();
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
		final AppHyperEdge[] oldOutHypEdges = oldNode.getOutgoingHyperEdges().toArray(new AppHyperEdge[] {});
		for (final AppHyperEdge oldOutHypEdge : oldOutHypEdges) {
			final AnnotatedProgramPoint source = oldOutHypEdge.getSource();
			final AnnotatedProgramPoint target = oldOutHypEdge.getTarget();
			final Return statement = (Return) oldOutHypEdge.getStatement();

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

	private void makeConnections() {
		for (final Entry<AnnotatedProgramPoint, HashMap<CodeBlock, AnnotatedProgramPoint>> pre2 : _pre2stm2post_toConnectIfSat
				.entrySet()) {
			for (final Entry<CodeBlock, AnnotatedProgramPoint> stm2 : pre2.getValue().entrySet()) {
				if (isSatEdge(pre2.getKey().getPredicate(), stm2.getKey(), stm2.getValue().getPredicate())) {
					pre2.getKey().connectOutgoing(stm2.getKey(), stm2.getValue());
				}
			}
		}

		for (final Entry<AnnotatedProgramPoint, HashMap<AnnotatedProgramPoint, HashMap<Return, AnnotatedProgramPoint>>> pre2 : _pre2hier2stm2post_toConnectIfSat
				.entrySet()) {
			for (final Entry<AnnotatedProgramPoint, HashMap<Return, AnnotatedProgramPoint>> hier2 : pre2.getValue()
					.entrySet()) {
				for (final Entry<Return, AnnotatedProgramPoint> stm2 : hier2.getValue().entrySet()) {
					if (isSatRetEdge(pre2.getKey().getPredicate(), hier2.getKey().getPredicate(), stm2.getKey(), stm2
							.getValue().getPredicate())) {
						pre2.getKey().connectOutgoingReturn(hier2.getKey(), stm2.getKey(), stm2.getValue());
					}
				}
			}
		}
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
		if (statement instanceof DummyCodeBlock) {
			return false;
		}

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
		if (statement instanceof Call) {
			//result is true if pre /\ stm /\ post is sat or unknown, false if unsat 
			result = _edgeChecker.checkCall(preCondition, (ICallAction) statement, negatePredicateNoPU(postCondition)) != Validity.VALID;
		} else {
			result = _edgeChecker.checkInternal(preCondition, (IInternalAction) statement, negatePredicateNoPU(postCondition)) != Validity.VALID;
		}

		if (GlobalSettings._instance._memoizeNormalEdgeChecks) {
			if (result) {
				_satTriples.put(preCondition, statement, postCondition, IsContained.IsContained);
			} else {
				_unsatTriples.put(preCondition, statement, postCondition, IsContained.IsContained);
			}
		}

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

		final boolean result = _edgeChecker.checkReturn(preCondition, hier, statement,
				negatePredicateNoPU(postCondition)) != Validity.VALID;

		if (GlobalSettings._instance._memoizeReturnEdgeChecks) {
			if (result) {
				_satQuadruples.put(preCondition, hier, statement, postCondition, IsContained.IsContained);
			} else {
				_unsatQuadruples.put(preCondition, hier, statement, postCondition, IsContained.IsContained);
			}
		}

		return result;
	}

}
