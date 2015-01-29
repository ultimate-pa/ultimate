package de.uni_freiburg.informatik.ultimate.boogie.procedureinliner;

import java.util.Collection;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.access.IUnmanagedObserver;
import de.uni_freiburg.informatik.ultimate.access.WalkerOptions;
import de.uni_freiburg.informatik.ultimate.boogie.procedureinliner.callgraph.CallGraphBuildException;
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
	
	private Unit mAstUnit;
	private Collection<Declaration> mNonProcedureDeclarations;
	private Map<String, CallGraphNode> mCallGraph;
	List<CallGraphNode> mReversedTopologicalOrdering;
	
	public Inliner(IUltimateServiceProvider services) {
		mServices = services;
	}
	
	@Override
	public void init() {
	}

	@Override
	public void finish() {
	}

	@Override
	public WalkerOptions getWalkerOptions() {
		return null;
	}

	@Override
	public boolean performedChanges() {
		return true; // assumption
	}

	@Override
	public boolean process(IElement root) throws Throwable {
		if (!mProgressMonitorService.continueProcessing()) {
			return false;
		} else if (root instanceof Unit) {
			mAstUnit = (Unit) root;
			inline();
			return false;
		} else {
			return true;
		}
	}

	private void inline() {
		try {
			buildCallGraph();
		} catch (CallGraphBuildException buildException) {
			buildException.logErrorAndCancelToolchain(mServices, Activator.PLUGIN_ID);
			return;
		}
		// TODO inline procedures, using the call graph
		// TODO build new ast Unit using the inlined procedures and nonProcedureDeclarations
	}
	
	private void buildCallGraph() throws CallGraphBuildException {
		CallGraphBuilder callGraphBuilder = new CallGraphBuilder();
		callGraphBuilder.buildCallGraph(mAstUnit);
		mCallGraph = callGraphBuilder.getCallGraph();
		mNonProcedureDeclarations = callGraphBuilder.getNonProcedureDeclarations();
		mReversedTopologicalOrdering = new TopologicalSorter<CallGraphNode, CallGraphEdgeLabel>(new SimpleCallFilter())
				.reversedTopologicalOrdering(mCallGraph.values());
	}

}
