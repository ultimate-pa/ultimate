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

import de.uni_freiburg.informatik.ultimate.access.IUnmanagedObserver;
import de.uni_freiburg.informatik.ultimate.access.WalkerOptions;
import de.uni_freiburg.informatik.ultimate.boogie.procedureinliner.Activator;
import de.uni_freiburg.informatik.ultimate.boogie.procedureinliner.callgraph.CallGraphEdgeLabel.EdgeType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.TarjanSCC;
import de.uni_freiburg.informatik.ultimate.core.services.IProgressMonitorService;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.*;
import de.uni_freiburg.informatik.ultimate.model.location.ILocation;
import de.uni_freiburg.informatik.ultimate.result.IResult;
import de.uni_freiburg.informatik.ultimate.result.SyntaxErrorResult;
import de.uni_freiburg.informatik.ultimate.result.UnsupportedSyntaxResult;

public class CallGraphBuilder implements IUnmanagedObserver {
	
	private IUltimateServiceProvider mServices;
	private IProgressMonitorService mProgressMonitorService;
	
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
	
	public CallGraphBuilder(IUltimateServiceProvider services) {
		mServices = services;
		mProgressMonitorService = services.getProgressMonitorService();
	}
	
	@Override
	public void init() {
		mNonProcedureDeclarations = new ArrayList<Declaration>();
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
		if(!mProgressMonitorService.continueProcessing()) {
			return false;
		} else if (element instanceof Procedure) {
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
		mNonProcedureDeclarations = Collections.unmodifiableCollection(mNonProcedureDeclarations);
		mCallGraphNodes = Collections.unmodifiableMap(mCallGraphNodes);
		findRecursiveComponents();
		setAllEdgeTypes();
	}

	@Override
	public boolean performedChanges() {
		return false;
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
	
	private void processProcedure(Procedure procedure) {
		String procedureId = procedure.getIdentifier();
		CallGraphNode node = getOrCreateNode(procedureId);
		if (procedure.getSpecification() != null) {
			if (node.getProcedureWithSpecification() == null) {
				node.setProcedureWithSpecification(procedure);				
			} else {
				multipleDeclarationsError(procedure);
			}
		}
		if (procedure.getBody() != null) {
			if (node.getProcedureWithBody() == null) {
				node.setProcedureWithBody(procedure);
				registerCallStatementsInGraph(node, procedure.getBody().getBlock());				
			} else {
				multipleImplementationsError(procedure);
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
	
	private void multipleDeclarationsError(Procedure procDecl) {
		String description = "Procedure was already declared: " + procDecl.getIdentifier();
		syntaxError(procDecl.getLocation(), description);
	}
	
	private void syntaxError(ILocation location, String description) {
		errorAndAbort(location, description, new SyntaxErrorResult(Activator.PLUGIN_ID, location, description));
	}
	
	private void multipleImplementationsError(Procedure procImpl) {
		String description = "Multiple procedure implementations aren't supported: " + procImpl.getIdentifier();
		unsupportedSyntaxError(procImpl.getLocation(), description);
	}
	
	private void unsupportedSyntaxError(ILocation location, String description) {
		errorAndAbort(location, description,
				new UnsupportedSyntaxResult<Procedure>(Activator.PLUGIN_ID, location, description));
	}
	
	/**
	 * Prints an error to the log and cancels the tool chain with the given result.
	 * @param location Location of the error.
	 * @param description Description of the error.
	 * @param error Error result.
	 */
	private void errorAndAbort(ILocation location, String description, IResult error) {
		String pluginId = Activator.PLUGIN_ID;
		mServices.getLoggingService().getLogger(pluginId).error(location + ": " + description);
		mServices.getResultService().reportResult(pluginId, error);
		mProgressMonitorService.cancelToolchain();
	}

}
