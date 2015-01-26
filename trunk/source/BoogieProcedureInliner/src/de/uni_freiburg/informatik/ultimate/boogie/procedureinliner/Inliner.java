package de.uni_freiburg.informatik.ultimate.boogie.procedureinliner;

import java.util.Collection;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.access.IUnmanagedObserver;
import de.uni_freiburg.informatik.ultimate.access.WalkerOptions;
import de.uni_freiburg.informatik.ultimate.boogie.procedureinliner.callgraph.CallGraphBuilder;
import de.uni_freiburg.informatik.ultimate.boogie.procedureinliner.callgraph.CallGraphEdgeLabel;
import de.uni_freiburg.informatik.ultimate.boogie.procedureinliner.callgraph.CallGraphNode;
import de.uni_freiburg.informatik.ultimate.boogie.procedureinliner.callgraph.SimpleCallFilter;
import de.uni_freiburg.informatik.ultimate.boogie.procedureinliner.callgraph.TopologicalSorter;
import de.uni_freiburg.informatik.ultimate.core.services.IProgressMonitorService;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.*;

public class Inliner implements IUnmanagedObserver {

	private IUltimateServiceProvider mServices;
	private IProgressMonitorService mProgressMonitorService;
	
	private CallGraphBuilder mCallGraphBuilder;
	private Map<String, CallGraphNode> mCallGraph;
	private Collection<Declaration> mNonProcedureDeclarations;
	
	
	public Inliner(IUltimateServiceProvider services, CallGraphBuilder callGraphBuilder) {
		mServices = services;
		mProgressMonitorService = services.getProgressMonitorService();
		mCallGraphBuilder = callGraphBuilder;
	}
	
	@Override
	public void init() {
		mCallGraph = mCallGraphBuilder.getCallGraph();
		mNonProcedureDeclarations = mCallGraphBuilder.getNonProcedureDeclarations();
	}

	@Override
	public void finish() {
	}

	@Override
	public WalkerOptions getWalkerOptions() {
		if(mProgressMonitorService.continueProcessing()) {
			List<CallGraphNode> topologicalOrdering = new TopologicalSorter<CallGraphNode, CallGraphEdgeLabel>(
					new SimpleCallFilter()).sortTopological(mCallGraph.values());
			// TODO inline procedures, using the call graph
			// TODO build new ast Unit using the inlined procedures and nonProcedureDeclarations
		}
		return null;
	}

	@Override
	public boolean performedChanges() {
		return false;
	}

	@Override
	public boolean process(IElement root) throws Throwable {
		return false;
	}

}
