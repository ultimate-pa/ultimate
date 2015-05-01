package de.uni_freiburg.informatik.ultimate.boogie.procedureinliner;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.access.IUnmanagedObserver;
import de.uni_freiburg.informatik.ultimate.access.WalkerOptions;
import de.uni_freiburg.informatik.ultimate.boogie.procedureinliner.backtranslation.InlinerBacktranslator;
import de.uni_freiburg.informatik.ultimate.boogie.procedureinliner.callgraph.CallGraphBuilder;
import de.uni_freiburg.informatik.ultimate.boogie.procedureinliner.callgraph.CallGraphNode;
import de.uni_freiburg.informatik.ultimate.boogie.procedureinliner.callgraph.NodeLabeler;
import de.uni_freiburg.informatik.ultimate.boogie.procedureinliner.exceptions.CancelToolchainException;
import de.uni_freiburg.informatik.ultimate.boogie.procedureinliner.preferences.PreferenceItem;
import de.uni_freiburg.informatik.ultimate.boogie.procedureinliner.preferences.PreferencesInlineSelector;
import de.uni_freiburg.informatik.ultimate.core.services.IProgressMonitorService;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.model.GraphType;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.*;

/**
 * Observer, which builds a call graph, sets inline flags of procedures and inlines the flagged procedures.
 * 
 * @author schaetzc@informatik.uni-freiburg.de
 */
public class Inliner implements IUnmanagedObserver {

	private IUltimateServiceProvider mServices;
	private IProgressMonitorService mProgressMonitorService;

	private IInlineSelector mInlineSelector;
	private NodeLabeler mNodeLabeler;
	
	private Unit mAstUnit;
	private Collection<Declaration> mNonProcedureDeclarations;
	private Map<String, CallGraphNode> mCallGraph;

	private Set<String> mEntryAndReEntryProcedures;
	private Map<String, Procedure> mNewProceduresWithBody;
	
	private InlinerBacktranslator mBacktranslator;
	
	/**
	 * Creates a new observer, which inlines Boogie procedures.
	 * @param services Service provider.
	 */
	public Inliner(IUltimateServiceProvider services) {
		mServices = services;
		mProgressMonitorService = services.getProgressMonitorService();
		mInlineSelector = new PreferencesInlineSelector();
		mNodeLabeler = new NodeLabeler(PreferenceItem.ENTRY_PROCEDURES.getStringValueTokens());
		mBacktranslator = new InlinerBacktranslator(services);
	}

	@Override
	public void init(GraphType modelType, int currentModelIndex, int numberOfModels) {
		mNewProceduresWithBody = new HashMap<String, Procedure>();
	}

	@Override
	public void finish() {
		mServices.getBacktranslationService().addTranslator(mBacktranslator);
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
				inline();
			} catch (CancelToolchainException cte) {
				cte.logErrorAndCancelToolchain(mServices, Activator.PLUGIN_ID);
			}
			return false;
		} else {
			return true;
		}
	}

	private void inline() throws CancelToolchainException {
		buildCallGraph();

		InlineVersionTransformer.GlobalScopeManager globalScopeManager =
				new InlineVersionTransformer.GlobalScopeManager(mNonProcedureDeclarations);
		boolean assumeRequiresAfterAssert = PreferenceItem.ASSUME_REQUIRES_AFTER_ASSERT.getBooleanValue();
		boolean assertEnsuresBeforeAssume = PreferenceItem.ASSERT_ENSURES_BEFORE_ASSUME.getBooleanValue();
		for (CallGraphNode node : proceduresToBeProcessed()) {
			if (node.isImplemented() && node.hasInlineFlags()) {
				InlineVersionTransformer transformer = new InlineVersionTransformer(mServices,
						globalScopeManager, assumeRequiresAfterAssert, assertEnsuresBeforeAssume);
				mNewProceduresWithBody.put(node.getId(), transformer.inlineCallsInside(node));
				mBacktranslator.addBacktranslation(transformer);
			}
		}
		writeNewDeclarationsToAstUnit();
	}
	
	private void buildCallGraph() throws CancelToolchainException {
		CallGraphBuilder callGraphBuilder = new CallGraphBuilder();
		callGraphBuilder.buildCallGraph(mAstUnit);
		mCallGraph = callGraphBuilder.getCallGraph();
		mNonProcedureDeclarations = callGraphBuilder.getNonProcedureDeclarations();
		
		mInlineSelector.setInlineFlags(mCallGraph);
		mEntryAndReEntryProcedures = mNodeLabeler.label(mCallGraph);
	}
	
	private Collection<CallGraphNode> proceduresToBeProcessed() {
		Collection<CallGraphNode> proceduresToBeProcessed;
		if (PreferenceItem.PROCESS_ONLY_ENTRY_AND_REENTRY_PROCEDURES.getBooleanValue()) {
			proceduresToBeProcessed = new ArrayList<>(mEntryAndReEntryProcedures.size());
			for (String procId : mEntryAndReEntryProcedures) {
				proceduresToBeProcessed.add(mCallGraph.get(procId));
			}
		} else {
			proceduresToBeProcessed = mCallGraph.values();
		}
		return proceduresToBeProcessed;
	}
	
	private void writeNewDeclarationsToAstUnit() {
		List<Declaration> newDeclarations = new ArrayList<>();
		newDeclarations.addAll(mNonProcedureDeclarations);
		boolean eliminateDeadCode = PreferenceItem.ELIMINATE_DEAD_CODE.getBooleanValue();
		for (CallGraphNode node : mCallGraph.values()) {
			if (eliminateDeadCode && !mEntryAndReEntryProcedures.contains(node.getId())) {
				continue;
			}
			Procedure oldProcWithSpec = node.getProcedureWithSpecification();
			Procedure oldProcWithBody = node.getProcedureWithBody();
			Procedure newProcWithBody = mNewProceduresWithBody.get(node.getId());
			if (newProcWithBody == null) { // the procedure had nothing to inline, nothing changed
				newDeclarations.add(oldProcWithSpec);
				if (node.isImplemented() && !node.isCombined()) {
					newDeclarations.add(oldProcWithBody);
				}
			} else {
				if (!node.isCombined()) {
					newDeclarations.add(oldProcWithSpec);
				}
				newDeclarations.add(newProcWithBody);
			}
		}
		mAstUnit.setDeclarations(newDeclarations.toArray(new Declaration[newDeclarations.size()]));
	}
}
