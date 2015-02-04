package de.uni_freiburg.informatik.ultimate.boogie.procedureinliner;

import java.util.Collection;
import java.util.Map;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.access.IUnmanagedObserver;
import de.uni_freiburg.informatik.ultimate.access.WalkerOptions;
import de.uni_freiburg.informatik.ultimate.boogie.procedureinliner.callgraph.CallGraphBuildException;
import de.uni_freiburg.informatik.ultimate.boogie.procedureinliner.callgraph.CallGraphBuilder;
import de.uni_freiburg.informatik.ultimate.boogie.procedureinliner.callgraph.CallGraphNode;
import de.uni_freiburg.informatik.ultimate.core.services.IProgressMonitorService;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.*;

public class Inliner implements IUnmanagedObserver {

	private IUltimateServiceProvider mServices;
	private Logger mLogger;
	private IProgressMonitorService mProgressMonitorService;
	
	private IInlineSelector mInlineSelector;
	
	private Unit mAstUnit;
	private Collection<Declaration> mNonProcedureDeclarations;
	private Map<String, CallGraphNode> mCallGraph;
	
	/**
	 * Creates a new observer, which inlines Boogie procedures.
	 * @param services Service provider.
	 * @param inlineSelector Selector, which sets the inline flags for all edges of the call graph.
	 */
	public Inliner(IUltimateServiceProvider services, IInlineSelector inlineSelector) {
		mServices = services;
		mLogger = services.getLoggingService().getLogger(Activator.PLUGIN_ID);
		mProgressMonitorService = services.getProgressMonitorService();
		mInlineSelector = inlineSelector;
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
			
			try {
				buildCallGraph();
			} catch (CallGraphBuildException buildException) {
				buildException.logErrorAndCancelToolchain(mServices, Activator.PLUGIN_ID);
				return false;
			}
			
			mInlineSelector.setInlineFlags(mCallGraph);

			for (CallGraphNode node : mCallGraph.values()) {
				Procedure procDecl = node.getProcedureWithSpecification();
				Procedure procImpl = node.getProcedureWithBody();
				if (node.getOutgoingEdgeLabels().isEmpty()) {
					continue;
				}
				// TODO inline procedures
			}

			// TODO build new ast Unit using the inlined procedures and nonProcedureDeclarations			
			
			return false;
		} else {
			return true;
		}
	}
	
	private void buildCallGraph() throws CallGraphBuildException {
		CallGraphBuilder callGraphBuilder = new CallGraphBuilder();
		callGraphBuilder.buildCallGraph(mAstUnit);
		mCallGraph = callGraphBuilder.getCallGraph();
		mNonProcedureDeclarations = callGraphBuilder.getNonProcedureDeclarations();
	}

}
