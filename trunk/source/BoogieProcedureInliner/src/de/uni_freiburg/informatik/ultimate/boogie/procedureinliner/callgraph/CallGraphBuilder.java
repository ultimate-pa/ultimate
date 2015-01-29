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

import de.uni_freiburg.informatik.ultimate.boogie.procedureinliner.callgraph.CallGraphEdgeLabel.EdgeType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.TarjanSCC;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.*;

public class CallGraphBuilder {
	
	/** All Declarations from the last processed Boogie ast, other than Procedures. */
	private Collection<Declaration> mNonProcedureDeclarations;

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

	/**
	 * Creates a call graph for a given Boogie ast.
	 * The graph contains all procedures and implementations.
	 * All other declarations from the Boogie ast are separately stored.
	 * @param boogieAstUnit Boogie ast.
	 * @throws CallGraphBuildException A procedure had multiple declarations or implementations.
	 * @see #getCallGraph()
	 * @see #getNonProcedureDeclarations()
	 */
	public void buildCallGraph(Unit boogieAstUnit) throws CallGraphBuildException {
		init();
		for (Declaration declaration : boogieAstUnit.getDeclarations()) {
			if (declaration instanceof Procedure) {
				processProcedure((Procedure) declaration);
			} else {
				mNonProcedureDeclarations.add(declaration);
			}
		}
		finish();
	}

	/**
	 * Gets the builded call graph, containing all Boogie Procedures from the last run.
	 * The Procedure identifiers are used as keys. The values are the nodes from the call graph.
	 * @return Call graph from the last run.
	 */
	public Map<String, CallGraphNode> getCallGraph() {
		return mCallGraphNodes;
	}
	
	/**
	 * Gets all the Boogie declarations from the last run, other than Procedures. 
	 * @return Non-Procedure Boogie Declarations.
	 */
	public Collection<Declaration> getNonProcedureDeclarations() {
		return mNonProcedureDeclarations;
	}
	
	public void init() {
		mNonProcedureDeclarations = new ArrayList<Declaration>();
		mCallGraphNodes = new HashMap<String, CallGraphNode>();
		mRecursiveComponents = null;
		mRecursiveProcedures = null;
	}

	public void finish() {
		mNonProcedureDeclarations = Collections.unmodifiableCollection(mNonProcedureDeclarations);
		mCallGraphNodes = Collections.unmodifiableMap(mCallGraphNodes);
		findRecursiveComponents();
		setAllEdgeTypes();
	}
	
	private void processProcedure(Procedure procedure) throws CallGraphBuildException {
		String procedureId = procedure.getIdentifier();
		CallGraphNode node = getOrCreateNode(procedureId);
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
			List<CallGraphNode> outgoingNodes = node.getOutgoingNodes();
			List<CallGraphEdgeLabel> outgoingEdgeLabels = node.getOutgoingEdgeLabels();
			for (int i = 0; i < outgoingNodes.size(); ++i) {
				if (outgoingEdgeLabels.get(i).getEdgeType() != EdgeType.CALL_FORALL) {
					simpleOutgoingNodesRepresentation.add(outgoingNodes.get(i).getId());					
				}
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
			return calleeNode.getProcedureWithBody() == null ?
					EdgeType.SIMPLE_CALL_UNIMPLEMENTED : EdgeType.SIMPLE_CALL_IMPLEMENTED;
		} else {
			return callerRecursiveComponent == calleeRecursiveComponent ?
					EdgeType.INTERN_RECURSIVE_CALL : EdgeType.EXTERN_RECURSIVE_CALL;
		}
	}

	/**
	 * Returns the recursive component of the procedure with the given id.
	 * The same object is returned for all procedures of the same component, so reference equality can be used.
	 * @param procedureId Identifier of a procedure.
	 * @return The procedures recursive component or null, if it isn't recursive.
	 */
	private Set<String> recursiveComponentOf(String procedureId) {
		for (Set<String> component : mRecursiveComponents) {
			if (component.contains(procedureId)) {
				return component;
			}
		}
		return null;
	}

}
