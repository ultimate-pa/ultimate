package de.uni_freiburg.informatik.ultimate.boogie.procedureinliner;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.access.IUnmanagedObserver;
import de.uni_freiburg.informatik.ultimate.access.WalkerOptions;
import de.uni_freiburg.informatik.ultimate.boogie.procedureinliner.callgraph.CallGraphBuildException;
import de.uni_freiburg.informatik.ultimate.boogie.procedureinliner.callgraph.CallGraphBuilder;
import de.uni_freiburg.informatik.ultimate.boogie.procedureinliner.callgraph.CallGraphEdgeLabel;
import de.uni_freiburg.informatik.ultimate.boogie.procedureinliner.callgraph.CallGraphNode;
import de.uni_freiburg.informatik.ultimate.core.services.IProgressMonitorService;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.model.IType;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.*;

public class Inliner implements IUnmanagedObserver {

	private IUltimateServiceProvider mServices;
	private IProgressMonitorService mProgressMonitorService;
	private Logger mLogger;

	private IInlineSelector mInlineSelector;

	private Unit mAstUnit;
	private Collection<Declaration> mNonProcedureDeclarations;
	private Map<String, CallGraphNode> mCallGraph;

	private Map<String, Procedure> mNewProceduresWithBody;

	/**
	 * Creates a new observer, which inlines Boogie procedures.
	 * 
	 * @param services
	 *            Service provider.
	 * @param inlineSelector
	 *            Selector, which sets the inline flags for all edges of the
	 *            call graph.
	 */
	public Inliner(IUltimateServiceProvider services, IInlineSelector inlineSelector) {
		mServices = services;
		mProgressMonitorService = services.getProgressMonitorService();
		mLogger = services.getLoggingService().getLogger(Activator.PLUGIN_ID);
		mInlineSelector = inlineSelector;
	}

	@Override
	public void init() {
		mNewProceduresWithBody = new HashMap<String, Procedure>();
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
		mInlineSelector.setInlineFlags(mCallGraph);

		InlineVersionTransformer.GlobalScopeInitializer globalScopeInit =
				new InlineVersionTransformer.GlobalScopeInitializer(mNonProcedureDeclarations);
		for (CallGraphNode node : mCallGraph.values()) {
			if (node.isImplemented() && containsCallsToBeInlined(node)) {
				InlineVersionTransformer transformer = new InlineVersionTransformer(mServices, globalScopeInit);
				mNewProceduresWithBody.put(node.getId(), transformer.process(node));
			}
		}
		writeNewDeclarationsToAstUnit();
	}

	private void buildCallGraph() throws CallGraphBuildException {
		CallGraphBuilder callGraphBuilder = new CallGraphBuilder();
		callGraphBuilder.buildCallGraph(mAstUnit);
		mCallGraph = callGraphBuilder.getCallGraph();
		mNonProcedureDeclarations = callGraphBuilder.getNonProcedureDeclarations();
	}

	private void writeNewDeclarationsToAstUnit() {
		List<Declaration> newDeclarations = new ArrayList<>();
		newDeclarations.addAll(mNonProcedureDeclarations);
		for (CallGraphNode node : mCallGraph.values()) {
			Procedure oldProcWithSpec = node.getProcedureWithSpecification();
			Procedure oldProcWithBody = node.getProcedureWithBody();
			Procedure newProcWithBody = mNewProceduresWithBody.get(node.getId());
			if (newProcWithBody == null) {
				newDeclarations.add(oldProcWithSpec);
				if (node.isImplemented() && oldProcWithBody != oldProcWithSpec) {
					newDeclarations.add(oldProcWithBody);
				}
			} else {
				if (newProcWithBody.getSpecification() == null) {
					assert oldProcWithSpec.getBody() == null;
					newDeclarations.add(oldProcWithSpec);
				}
				newDeclarations.add(newProcWithBody);
			}
		}
		mAstUnit.setDeclarations(newDeclarations.toArray(new Declaration[newDeclarations.size()]));
	}

	private boolean containsCallsToBeInlined(CallGraphNode node) {
		for (CallGraphEdgeLabel outgoingEdgeLabel : node.getOutgoingEdgeLabels()) {
			if (outgoingEdgeLabel.getInlineFlag()) {
				return true;
			}
		}
		return false;
	}

}
