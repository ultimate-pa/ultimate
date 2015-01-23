package de.uni_freiburg.informatik.ultimate.boogie.procedureinliner.callgraph;

import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.access.IUnmanagedObserver;
import de.uni_freiburg.informatik.ultimate.access.WalkerOptions;
import de.uni_freiburg.informatik.ultimate.boogie.procedureinliner.Activator;
import de.uni_freiburg.informatik.ultimate.boogie.procedureinliner.callgraph.CallGraphEdgeLabel.EdgeType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.TarjanSCC;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.*;

public class CallGraphBuilder implements IUnmanagedObserver {
	
	private IUltimateServiceProvider mServices;

	/** All Declarations from the last processed Boogie ast, other than Procedures. */
	private Set<Declaration> mNonProcedureDeclarations;

	/**
	 * All nodes from the call graph of the last processed Boogie program.
	 * The procedure identifiers are used as keys, the nodes are the values.
	 * The nodes represent the procedures, the directed edges represent the calls from callers to the callees.
	 */
	private Map<String, CallGraphNode> mCallGraphNodes;
	
	/**
	 * The recursive components of this call graph. A component is denoted by a set of procedure ids.
	 * Recursive components are similar the the strongly connected components of the graph,
	 * ignoring "call forall" edges and singleton components without self-loops.
	 */
	private Set<Set<String>> mRecursiveComponents;
	
	/** Flat view of {@link #mRecursiveComponents}. */
	private Set<String> mRecursiveProcedures;

	
	public CallGraphBuilder(IUltimateServiceProvider services) {
		mServices = services;
	}
	
	@Override
	public void init() {
		mNonProcedureDeclarations = new HashSet<Declaration>();
		mCallGraphNodes = new HashMap<String, CallGraphNode>();
		mRecursiveComponents = null;
		mRecursiveProcedures = null;
	}

	@Override
	public WalkerOptions getWalkerOptions() {
		return null;
	}

	@Override
	public boolean process(IElement element) throws Throwable {
		if (element instanceof Procedure) {
			processProcedure((Procedure) element);
			return false;
		} else if (element instanceof Declaration) {
			mNonProcedureDeclarations.add((Declaration) element);
			return false;
		}
		return true;
	}

	@Override
	public void finish() {
		mCallGraphNodes = Collections.unmodifiableMap(mCallGraphNodes);
		findRecursiveComponents();
		setAllEdgeTypes();
	}

	@Override
	public boolean performedChanges() {
		return false;
	}

	private void processProcedure(Procedure procedure) {
		String procedureId = procedure.getIdentifier();
		CallGraphNode node = getOrCreateNode(procedureId);
		if (procedure.getSpecification() != null) {
			if (node.getProcedureWithSpecification() == null) {
				node.setProcedureWithSpecification(procedure);				
			} else {
				// ERROR, procedure was already defined/specified
			}
		}
		if (procedure.getBody() != null) {
			if (node.getProcedureWithBody() == null) {
				node.setProcedureWithBody(procedure);
				registerCallStatementsInGraph(node, procedure.getBody().getBlock());				
			} else {
				// ERROR, procedure was already implemented (multiple implementations aren't supported)
			}
		}
	}

	private CallGraphNode getOrCreateNode(String procedureId) {
		CallGraphNode node = mCallGraphNodes.get(procedureId);
		if (node == null) {
			node = new CallGraphNode(procedureId);
			mCallGraphNodes.put(procedureId, node);
		}
		return node;
	}
	
	
	private void registerCallStatementsInGraph(CallGraphNode callerNode, Statement[] statementBlock) {
		for (Statement statement : statementBlock) {
			if (statement instanceof CallStatement) {
				registerCallStatementInGraph(callerNode, (CallStatement) statement);
			} else if (statement instanceof IfStatement) {
				IfStatement ifStatement = (IfStatement) statement;
				registerCallStatementsInGraph(callerNode, ifStatement.getThenPart());
				registerCallStatementsInGraph(callerNode, ifStatement.getElsePart());
			} else if (statement instanceof WhileStatement) {
				WhileStatement whileStatement = (WhileStatement) statement;
				registerCallStatementsInGraph(callerNode, whileStatement.getBody());
			}
			// else, assume statement contains no other statements
		}
	}
	
	private void registerCallStatementInGraph(CallGraphNode callerNode, CallStatement callStatement) {
		CallGraphNode calleeNode = getOrCreateNode(callStatement.getMethodName());
		EdgeType edgeType = callStatement.isForall() ? EdgeType.CALL_FORALL : null;
		callerNode.addOutgoingNode(calleeNode, new CallGraphEdgeLabel(calleeNode.getId(), edgeType));
		calleeNode.addIncomingNode(callerNode);
	}

	private void findRecursiveComponents() {
		mRecursiveComponents = new HashSet<Set<String>>();
		mRecursiveProcedures = new HashSet<String>();
		for (Set<String> stronglyConnectedComponent : new TarjanSCC().getSCCs(buildSimpleGraphRepresentation())) {
			// components aren't empty, therefore this is equal to: (size==1) --> isDirectlyRecursive
			if (stronglyConnectedComponent.size() > 1 ||
					isDirectlyRecursive(stronglyConnectedComponent.iterator().next())) {
				mRecursiveComponents.add(Collections.unmodifiableSet(stronglyConnectedComponent));
				mRecursiveProcedures.addAll(stronglyConnectedComponent);
			}
		}
		mRecursiveComponents = Collections.unmodifiableSet(mRecursiveComponents);
		mRecursiveProcedures = Collections.unmodifiableSet(mRecursiveProcedures);
	}

	private boolean isDirectlyRecursive(String nodeId) {
		CallGraphNode node = mCallGraphNodes.get(nodeId);
		for(CallGraphNode outgoingNode : node.getOutgoingNodes()) {
			if (nodeId.equals(outgoingNode.getId())) {
				return true;
			}
		}
		return false;
	}
	
	private LinkedHashMap<String, LinkedHashSet<String>> buildSimpleGraphRepresentation() {
		LinkedHashMap<String, LinkedHashSet<String>> simpleGraphRepresentation = new LinkedHashMap<>();
		for (CallGraphNode node : mCallGraphNodes.values()) {
			String simpleNodeRepresentation = node.getId();
			LinkedHashSet<String> simpleOutgoingNodesRepresentation = new LinkedHashSet<>();
			for (CallGraphNode outgoingNode : node.getOutgoingNodes()) {
				simpleOutgoingNodesRepresentation.add(outgoingNode.getId());
			}
			simpleGraphRepresentation.put(simpleNodeRepresentation, simpleOutgoingNodesRepresentation);
		}
		return simpleGraphRepresentation;
	}
	
	private void setAllEdgeTypes() {
		for (CallGraphNode callerNode : mCallGraphNodes.values()) {
			Set<String> callerRecursiveComponent = recursiveComponentOf(callerNode.getId());
			List<CallGraphEdgeLabel> outgoingEdgeLabels = callerNode.getOutgoingEdgeLabels();
			for (int i = 0; i < outgoingEdgeLabels.size(); ++i) {
				CallGraphEdgeLabel label = outgoingEdgeLabels.get(i);
				String calleeProcedureId = label.getCalleeProcedureId();
				if (label.getEdgeType() != EdgeType.CALL_FORALL) {
					EdgeType edgeType = findEdgeTypeForNormalCall(callerRecursiveComponent, calleeProcedureId);
					outgoingEdgeLabels.set(i, new CallGraphEdgeLabel(calleeProcedureId, edgeType));
				}
			}
		}
	}

	private EdgeType findEdgeTypeForNormalCall(Set<String> callerRecursiveComponent, String calleeProcedureId) {
		CallGraphNode calleeNode = mCallGraphNodes.get(calleeProcedureId);
		Set<String> calleeRecursiveComponent = recursiveComponentOf(calleeProcedureId);
		if (calleeRecursiveComponent == null) {
			return callerRecursiveComponent == calleeRecursiveComponent ?
					EdgeType.INTERN_RECURSIVE_CALL : EdgeType.EXTERN_RECURSIVE_CALL;
		} else {
			return calleeNode.getProcedureWithBody() == null ?
					EdgeType.SIMPLE_CALL_UNIMPLEMENTED : EdgeType.SIMPLE_CALL_IMPLEMENTED;
		}
	}

	private Set<String> recursiveComponentOf(String procedureId) {
		for (Set<String> component : mRecursiveComponents) {
			if (component.contains(procedureId)) {
				return component;
			}
		}
		return null;
	}
	

}
