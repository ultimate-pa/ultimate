/*
 * Copyright (C) 2015 Claus Schaetzle (schaetzc@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE BoogieProcedureInliner plug-in.
 *
 * The ULTIMATE BoogieProcedureInliner plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE BoogieProcedureInliner plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE BoogieProcedureInliner plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE BoogieProcedureInliner plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE BoogieProcedureInliner plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.boogie.procedureinliner.callgraph;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.boogie.ast.AtomicStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.CallStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ForkStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IfStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Procedure;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Unit;
import de.uni_freiburg.informatik.ultimate.boogie.ast.WhileStatement;
import de.uni_freiburg.informatik.ultimate.boogie.procedureinliner.callgraph.CallGraphEdgeLabel.EdgeType;
import de.uni_freiburg.informatik.ultimate.boogie.procedureinliner.exceptions.CancelToolchainException;
import de.uni_freiburg.informatik.ultimate.boogie.procedureinliner.exceptions.MultipleImplementationsException;
import de.uni_freiburg.informatik.ultimate.boogie.procedureinliner.exceptions.ProcedureAlreadyDeclaredException;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.TarjanSCC;

/**
 * Builds a call graph of a boogie program.
 * <p>
 * Procedures are the nodes and calls are the edges. Every call has its own edge. The edges are labeled with the type of
 * the call (like normal, recursive and so on).
 * <p>
 * It is ensured that there is no procedure implementation without declaration and that there is at most one
 * implementation for every declaration (the latter is a restriction from the Inliner, not from the Boogie language).
 *
 * @see CallGraphNode
 * @see CallGraphEdgeLabel
 *
 * @author schaetzc@informatik.uni-freiburg.de
 */
public class CallGraphBuilder {

	/** All Declarations from the last processed Boogie ast, other than Procedures. */
	private Collection<Declaration> mNonProcedureDeclarations;

	/**
	 * All nodes from the call graph of the last processed Boogie program. The procedure identifiers are used as keys,
	 * the nodes are the values. The nodes represent the procedures, the directed edges represent the calls from callers
	 * to the callees.
	 */
	private Map<String, CallGraphNode> mCallGraphNodes;

	/**
	 * The recursive components of this call graph. A component is denoted by a set of procedure ids. Recursive
	 * components are similar the the strongly connected components of the graph, ignoring "call forall" edges and
	 * singleton components without self-loops.
	 */
	private Set<Set<String>> mRecursiveComponents;

	/** Flat view of {@link #mRecursiveComponents}. */
	private Set<String> mRecursiveProcedures;

	/**
	 * Creates a call graph for a given Boogie ast. The graph contains all procedures and implementations. All other
	 * declarations from the Boogie ast are separately stored.
	 *
	 * @param boogieAstUnit
	 *            Boogie ast.
	 * @throws CancelToolchainException
	 *             A procedure had multiple declarations or implementations.
	 * @see #getCallGraph()
	 * @see #getNonProcedureDeclarations()
	 */
	public void buildCallGraph(final Unit boogieAstUnit) throws CancelToolchainException {
		init();
		for (final Declaration declaration : boogieAstUnit.getDeclarations()) {
			if (declaration instanceof Procedure) {
				processProcedure((Procedure) declaration);
			} else {
				mNonProcedureDeclarations.add(declaration);
			}
		}
		finish();
	}

	/**
	 * Gets the builded call graph, containing all Boogie Procedures from the last run. The Procedure identifiers are
	 * used as keys. The values are the nodes from the call graph.
	 *
	 * @return Call graph from the last run.
	 */
	public Map<String, CallGraphNode> getCallGraph() {
		return mCallGraphNodes;
	}

	/**
	 * Gets all the Boogie declarations from the last run, other than Procedures.
	 *
	 * @return Non-Procedure Boogie Declarations.
	 */
	public Collection<Declaration> getNonProcedureDeclarations() {
		return mNonProcedureDeclarations;
	}

	public void init() {
		mNonProcedureDeclarations = new ArrayList<>();
		mCallGraphNodes = new HashMap<>();
		mRecursiveComponents = null;
		mRecursiveProcedures = null;
	}

	public void finish() {
		mNonProcedureDeclarations = Collections.unmodifiableCollection(mNonProcedureDeclarations);
		mCallGraphNodes = Collections.unmodifiableMap(mCallGraphNodes);
		findRecursiveComponents();
		setAllEdgeTypes();
	}

	private void processProcedure(final Procedure procedure) throws CancelToolchainException {
		final String procedureId = procedure.getIdentifier();
		final CallGraphNode node = getOrCreateNode(procedureId);
		if (procedure.getSpecification() != null) {
			if (node.getProcedureWithSpecification() == null) {
				node.setProcedureWithSpecification(procedure);
			} else {
				throw new ProcedureAlreadyDeclaredException(procedure);
			}
		}
		if (procedure.getBody() != null) {
			if (node.getProcedureWithBody() == null) {
				node.setProcedureWithBody(procedure);
				registerCallStatementsInGraph(node, procedure.getBody().getBlock());
			} else {
				throw new MultipleImplementationsException(procedure);
			}
		}
	}

	private CallGraphNode getOrCreateNode(final String procedureId) {
		CallGraphNode node = mCallGraphNodes.get(procedureId);
		if (node == null) {
			node = new CallGraphNode(procedureId);
			mCallGraphNodes.put(procedureId, node);
		}
		return node;
	}

	private void registerCallStatementsInGraph(final CallGraphNode callerNode, final Statement[] statementBlock) {
		for (final Statement statement : statementBlock) {
			if (statement instanceof CallStatement) {
				final CallStatement callStatement = (CallStatement) statement;
				final EdgeType edgeType = callStatement.isForall() ? EdgeType.CALL_FORALL : null;
				addEdge(callerNode, edgeType, callStatement.getMethodName());
			} else if (statement instanceof ForkStatement) {
				addEdge(callerNode, EdgeType.FORK, ((ForkStatement) statement).getProcedureName());
			} else if (statement instanceof IfStatement) {
				final IfStatement ifStatement = (IfStatement) statement;
				registerCallStatementsInGraph(callerNode, ifStatement.getThenPart());
				registerCallStatementsInGraph(callerNode, ifStatement.getElsePart());
			} else if (statement instanceof WhileStatement) {
				final WhileStatement whileStatement = (WhileStatement) statement;
				registerCallStatementsInGraph(callerNode, whileStatement.getBody());
			} else if (statement instanceof AtomicStatement) {
				final AtomicStatement atomicStatement = (AtomicStatement) statement;
				registerCallStatementsInGraph(callerNode, atomicStatement.getBody());
			}
			// else, assume statement contains no other statements
		}
	}

	private void addEdge(CallGraphNode callerNode, EdgeType edgeType, String calleeMethodName) {
		final CallGraphNode calleeNode = getOrCreateNode(calleeMethodName);
		callerNode.addOutgoingNode(calleeNode, new CallGraphEdgeLabel(calleeNode.getId(), edgeType));
		calleeNode.addIncomingNode(callerNode);
	}

	private void findRecursiveComponents() {
		mRecursiveComponents = new HashSet<>();
		mRecursiveProcedures = new HashSet<>();
		for (final Set<String> stronglyConnectedComponent : new TarjanSCC().getSCCs(buildSimpleGraphRepresentation())) {
			// components aren't empty, therefore this is equal to: (size==1) --> isDirectlyRecursive
			if (stronglyConnectedComponent.size() > 1
					|| isDirectlyRecursive(stronglyConnectedComponent.iterator().next())) {
				mRecursiveComponents.add(Collections.unmodifiableSet(stronglyConnectedComponent));
				mRecursiveProcedures.addAll(stronglyConnectedComponent);
			}
		}
		mRecursiveComponents = Collections.unmodifiableSet(mRecursiveComponents);
		mRecursiveProcedures = Collections.unmodifiableSet(mRecursiveProcedures);
	}

	private boolean isDirectlyRecursive(final String nodeId) {
		final CallGraphNode node = mCallGraphNodes.get(nodeId);
		for (final CallGraphNode outgoingNode : node.getOutgoingNodes()) {
			if (nodeId.equals(outgoingNode.getId())) {
				return true;
			}
		}
		return false;
	}

	private Map<String, Set<String>> buildSimpleGraphRepresentation() {
		final Map<String, Set<String>> simpleGraphRepresentation = new LinkedHashMap<>();
		for (final CallGraphNode node : mCallGraphNodes.values()) {
			final String simpleNodeRepresentation = node.getId();
			final LinkedHashSet<String> simpleOutgoingNodesRepresentation = new LinkedHashSet<>();
			final List<CallGraphNode> outgoingNodes = node.getOutgoingNodes();
			final List<CallGraphEdgeLabel> outgoingEdgeLabels = node.getOutgoingEdgeLabels();
			for (int i = 0; i < outgoingNodes.size(); ++i) {
				final EdgeType edgeType = outgoingEdgeLabels.get(i).getEdgeType();
				if (edgeType == null) {
					simpleOutgoingNodesRepresentation.add(outgoingNodes.get(i).getId());
				}
			}
			simpleGraphRepresentation.put(simpleNodeRepresentation, simpleOutgoingNodesRepresentation);
		}
		return simpleGraphRepresentation;
	}

	private void setAllEdgeTypes() {
		for (final CallGraphNode callerNode : mCallGraphNodes.values()) {
			final Set<String> callerRecursiveComponent = recursiveComponentOf(callerNode.getId());
			for (final CallGraphEdgeLabel label : callerNode.getOutgoingEdgeLabels()) {
				final String calleeProcedureId = label.getCalleeProcedureId();
				if (label.getEdgeType() == null) {
					label.setEdgeType(findEdgeTypeForNormalCall(callerRecursiveComponent, calleeProcedureId));
				}
			}
		}
	}

	private EdgeType findEdgeTypeForNormalCall(final Set<String> callerRecursiveComponent,
			final String calleeProcedureId) {
		final CallGraphNode calleeNode = mCallGraphNodes.get(calleeProcedureId);
		final Set<String> calleeRecursiveComponent = recursiveComponentOf(calleeProcedureId);
		if (calleeRecursiveComponent == null) {
			return calleeNode.getProcedureWithBody() == null ? EdgeType.SIMPLE_CALL_UNIMPLEMENTED
					: EdgeType.SIMPLE_CALL_IMPLEMENTED;
		}
		return callerRecursiveComponent == calleeRecursiveComponent ? EdgeType.INTERN_RECURSIVE_CALL
				: EdgeType.EXTERN_RECURSIVE_CALL;
	}

	/**
	 * Returns the recursive component of the procedure with the given id. The same object is returned for all
	 * procedures of the same component, so reference equality can be used.
	 *
	 * @param procedureId
	 *            Identifier of a procedure.
	 * @return The procedures recursive component or null, if it isn't recursive.
	 */
	private Set<String> recursiveComponentOf(final String procedureId) {
		for (final Set<String> component : mRecursiveComponents) {
			if (component.contains(procedureId)) {
				return component;
			}
		}
		return null;
	}

}
