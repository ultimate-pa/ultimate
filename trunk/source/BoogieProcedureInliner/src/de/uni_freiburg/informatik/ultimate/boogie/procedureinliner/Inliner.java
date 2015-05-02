package de.uni_freiburg.informatik.ultimate.boogie.procedureinliner;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.access.IUnmanagedObserver;
import de.uni_freiburg.informatik.ultimate.access.WalkerOptions;
import de.uni_freiburg.informatik.ultimate.boogie.procedureinliner.InlineVersionTransformer.GlobalScopeManager;
import de.uni_freiburg.informatik.ultimate.boogie.procedureinliner.backtranslation.InlinerBacktranslator;
import de.uni_freiburg.informatik.ultimate.boogie.procedureinliner.callgraph.CallGraphBuilder;
import de.uni_freiburg.informatik.ultimate.boogie.procedureinliner.callgraph.CallGraphNode;
import de.uni_freiburg.informatik.ultimate.boogie.procedureinliner.callgraph.CallGraphNodeLabel;
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
	private Logger mLogger;
	private IProgressMonitorService mProgressMonitorService;

	private IInlineSelector mInlineSelector;
	
	private Unit mAstUnit;
	private Collection<Declaration> mNonProcedureDeclarations;
	private Map<String, CallGraphNode> mCallGraph;

	private Map<String, Procedure> mNewProceduresWithBody;
	
	private InlinerBacktranslator mBacktranslator;
	
	/**
	 * Creates a new observer, which inlines Boogie procedures.
	 * @param services Service provider.
	 */
	public Inliner(IUltimateServiceProvider services) {
		mServices = services;
		mLogger = services.getLoggingService().getLogger(Activator.PLUGIN_ID);
		mProgressMonitorService = services.getProgressMonitorService();
		mInlineSelector = new PreferencesInlineSelector();
		mBacktranslator = new InlinerBacktranslator(services);
		mServices.getLoggingService().getLogger(Activator.PLUGIN_ID).info("Created inliner");
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

		GlobalScopeManager globalScopeManager = new GlobalScopeManager(mNonProcedureDeclarations);
		boolean assumeRequiresAfterAssert = PreferenceItem.ASSUME_REQUIRES_AFTER_ASSERT.getBooleanValue();
		boolean assertEnsuresBeforeAssume = PreferenceItem.ASSERT_ENSURES_BEFORE_ASSUME.getBooleanValue();
		for (CallGraphNode proc : proceduresToBeProcessed()) {
			if (proc.hasInlineFlags()) { // implies that the procedure is implemented
				InlineVersionTransformer transformer = new InlineVersionTransformer(mServices,
						globalScopeManager, assumeRequiresAfterAssert, assertEnsuresBeforeAssume);
				mNewProceduresWithBody.put(proc.getId(), transformer.inlineCallsInside(proc));
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
	}

	/**
	 * Creates the set of procedures to be processed by the InlinerVersionTransformer.
	 * <p>
	 * Note that some of the procedures might be unimplemented or have no inline flags.
	 * In this case, the don't have to be processed.
	 * 
	 * @return Procedures to be processed by the InlineVersionTransformer.
	 */
	private Collection<CallGraphNode> proceduresToBeProcessed() {
		if (!PreferenceItem.PROCESS_ONLY_ENTRY_AND_RE_ENTRY_PROCEDURES.getBooleanValue()) {
			return mCallGraph.values();
		}
		Collection<String> entryProcedures = PreferenceItem.ENTRY_PROCEDURES.getStringValueTokens();
		Collection<String> missingEntryProcedures = missingEntryProcedures(entryProcedures);
		if (missingEntryProcedures.size() == entryProcedures.size()) {
			mLogger.warn("Program contained no entry procedure!");
		}
		if (!missingEntryProcedures.isEmpty()) {
			mLogger.warn("Missing entry procedures: " + missingEntryProcedures);
		} else {
			return entryAndReEntryProcedures(entryProcedures);
		}
		
		if (PreferenceItem.ENTRY_PROCEDURE_FALLBACK.getBooleanValue()) {
			mLogger.warn("Fallback enabled. All procedures will be processed.");
			return mCallGraph.values();
		} else {
			mLogger.warn("Fallback not enabled! The resulting program might be not inlined or even empty.");
			return entryAndReEntryProcedures(entryProcedures);
		}
	}

	private Collection<String> missingEntryProcedures(Collection<String> procedureIds) {
		Collection<String> missingEntryProcedures = new ArrayList<>();
		for (String procedureId : procedureIds) {
			if (!mCallGraph.containsKey(procedureId)) {
				missingEntryProcedures.add(procedureId);
			}
		}
		return missingEntryProcedures;
	}

	private Collection<CallGraphNode> entryAndReEntryProcedures(Collection<String> entryProcedures) {
		NodeLabeler labeler = new NodeLabeler(entryProcedures);
		entryProcedures = labeler.label(mCallGraph);	
		Set<CallGraphNode> proceduresToBeProcessed = new HashSet<CallGraphNode>();
		for (String procId : entryProcedures) {
			CallGraphNode proc = mCallGraph.get(procId);
			proceduresToBeProcessed.add(proc);
		}
		return proceduresToBeProcessed;
	}
	
	private void writeNewDeclarationsToAstUnit() {
		List<Declaration> newDeclarations = new ArrayList<>();
		newDeclarations.addAll(mNonProcedureDeclarations);
		boolean eliminateDeadCode = PreferenceItem.ELIMINATE_DEAD_CODE.getBooleanValue();
		for (CallGraphNode proc : mCallGraph.values()) {
			// label might be null => NodeLabeler wasn't executed, => everything was processed => there is no dead code
			if (eliminateDeadCode && proc.getLabel() == CallGraphNodeLabel.DEAD) {
				continue;
			}
			Procedure oldProcWithSpec = proc.getProcedureWithSpecification();
			Procedure oldProcWithBody = proc.getProcedureWithBody();
			Procedure newProcWithBody = mNewProceduresWithBody.get(proc.getId());
			if (newProcWithBody == null) { // the procedure had nothing to inline, nothing changed
				newDeclarations.add(oldProcWithSpec);
				if (proc.isImplemented() && !proc.isCombined()) {
					newDeclarations.add(oldProcWithBody);
				}
			} else {
				if (!proc.isCombined()) {
					newDeclarations.add(oldProcWithSpec);
				}
				newDeclarations.add(newProcWithBody);
			}
		}
		mAstUnit.setDeclarations(newDeclarations.toArray(new Declaration[newDeclarations.size()]));
	}
}
