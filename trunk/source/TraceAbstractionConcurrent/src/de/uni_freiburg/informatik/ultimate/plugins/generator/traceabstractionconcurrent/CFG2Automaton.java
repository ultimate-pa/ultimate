/*
 * Copyright (C) 2013-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2011-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE TraceAbstractionConcurrent plug-in.
 *
 * The ULTIMATE TraceAbstractionConcurrent plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TraceAbstractionConcurrent plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceAbstractionConcurrent plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceAbstractionConcurrent plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TraceAbstractionConcurrent plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstractionconcurrent;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.BoogieIcfgContainer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.BoogieIcfgLocation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.StatementSequence;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Summary;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.preferences.RcfgPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.preferences.RcfgPreferenceInitializer.CodeBlockSize;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.PredicateFactory;

public abstract class CFG2Automaton {
	
	protected final ILogger mLogger;
	protected final IUltimateServiceProvider mServices;
	private final SimplificationTechnique mSimplificationTechnique;
	private final XnfConversionTechnique mXnfConversionTechnique;
	
	private final BoogieIcfgContainer mIcfg;
	private final CfgSmtToolkit mCsToolkit;
	private final PredicateFactory mPredicateFactory;
	private final IStateFactory<IPredicate> mContentFactory;
	protected ArrayList<INestedWordAutomaton<CodeBlock, IPredicate>> mAutomata;
	
	private CodeBlock mSharedVarsInit;
	private static final String mInitProcedure = "~init";
	
	public CFG2Automaton(final BoogieIcfgContainer rootAnnot, final IStateFactory<IPredicate> contentFactory,
			final CfgSmtToolkit csToolkit, final PredicateFactory predicateFactory,
			final IUltimateServiceProvider services, final SimplificationTechnique simplificationTechnique,
			final XnfConversionTechnique xnfConversionTechnique) {
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(Activator.PLUGIN_ID);
		mSimplificationTechnique = simplificationTechnique;
		mXnfConversionTechnique = xnfConversionTechnique;
		mIcfg = rootAnnot;
		mContentFactory = contentFactory;
		mCsToolkit = csToolkit;
		mPredicateFactory = predicateFactory;
	}
	
	public abstract Object getResult();
	
	protected void constructProcedureAutomata() {
		final CodeBlockSize codeBlockSize = RcfgPreferenceInitializer.getPreferences(mServices)
				.getEnum(RcfgPreferenceInitializer.LABEL_CodeBlockSize, RcfgPreferenceInitializer.CodeBlockSize.class);
		if (codeBlockSize != CodeBlockSize.SingleStatement) {
			throw new IllegalArgumentException("Concurrent programs reqire" + "atomic block encoding.");
		}
		
		if (!mIcfg.getBoogieDeclarations().getProcImplementation().containsKey(mInitProcedure)) {
			throw new IllegalArgumentException(
					"Concurrent program needs procedure " + mInitProcedure + " to initialize shared variables");
		}
		
		int numberOfProcedures;
		if (mIcfg.getBoogieDeclarations().getProcImplementation().containsKey(mInitProcedure)) {
			numberOfProcedures = mIcfg.getBoogieDeclarations().getProcImplementation().size() - 1;
			mLogger.debug("Program has procedure to initialize shared variables");
		} else {
			numberOfProcedures = mIcfg.getBoogieDeclarations().getProcImplementation().size();
			mLogger.debug("No procedure to initialize shared variables");
		}
		mLogger.debug("Found " + numberOfProcedures + "Procedures");
		
		mAutomata = new ArrayList<>(numberOfProcedures);
		
		mSharedVarsInit = extractPrecondition();
		
		for (final String proc : mIcfg.getBoogieDeclarations().getProcImplementation().keySet()) {
			if (proc.equals(mInitProcedure)) {
				continue;
			}
			final BoogieIcfgLocation entry = mIcfg.getProcedureEntryNodes().get(proc);
			mAutomata.add(getNestedWordAutomaton(entry));
		}
		assert mAutomata.size() == numberOfProcedures;
		
	}
	
	private CodeBlock extractPrecondition() {
		assert mIcfg.getBoogieDeclarations().getProcImplementation().containsKey(mInitProcedure);
		final BoogieIcfgLocation entry = mIcfg.getProcedureEntryNodes().get(mInitProcedure);
		final BoogieIcfgLocation exit = mIcfg.getProcedureExitNodes().get(mInitProcedure);
		final List<CodeBlock> codeBlocks = new ArrayList<>();
		
		BoogieIcfgLocation current = entry;
		while (current != exit) {
			assert current.getOutgoingEdges().size() == 1;
			assert current.getOutgoingEdges().get(0) instanceof StatementSequence;
			final StatementSequence succSS = (StatementSequence) current.getOutgoingEdges().get(0);
			assert succSS.getStatements().size() == 1;
			codeBlocks.add(succSS);
			current = (BoogieIcfgLocation) succSS.getTarget();
		}
		return mIcfg.getCodeBlockFactory().constructSequentialComposition(entry, exit, true, false, codeBlocks,
				mXnfConversionTechnique, mSimplificationTechnique);
	}
	
	/**
	 * Build NestedWordAutomaton for all code reachable from initial Node which is in the same procedure as initial
	 * Node. Initial Node does not have to be the enty Node of a procedure.
	 */
	private INestedWordAutomaton<CodeBlock, IPredicate> getNestedWordAutomaton(final BoogieIcfgLocation initialNode) {
		
		mLogger.debug("Step: Collect all LocNodes corresponding to" + " this procedure");
		
		final LinkedList<BoogieIcfgLocation> queue = new LinkedList<>();
		final Set<BoogieIcfgLocation> allNodes = new HashSet<>();
		queue.add(initialNode);
		allNodes.add(initialNode);
		
		while (!queue.isEmpty()) {
			final BoogieIcfgLocation currentNode = queue.removeFirst();
			
			if (currentNode.getOutgoingNodes() != null) {
				for (final IcfgLocation node : currentNode.getOutgoingNodes()) {
					final BoogieIcfgLocation nextNode = (BoogieIcfgLocation) node;
					if (!allNodes.contains(nextNode)) {
						allNodes.add(nextNode);
						queue.add(nextNode);
					}
				}
			}
		}
		
		mLogger.debug("Step: determine the alphabet");
		// determine the alphabet
		final Set<CodeBlock> internalAlphabet = new HashSet<>();
		final Set<CodeBlock> callAlphabet = new HashSet<>(0);
		final Set<CodeBlock> returnAlphabet = new HashSet<>(0);
		
		// add transAnnot from sharedVars initialization
		internalAlphabet.add(mSharedVarsInit);
		
		for (final BoogieIcfgLocation locNode : allNodes) {
			if (locNode.getOutgoingNodes() != null) {
				for (final IcfgEdge edge : locNode.getOutgoingEdges()) {
					if (edge instanceof Summary) {
						throw new IllegalArgumentException(
								"Procedure calls not" + " supported by concurrent trace abstraction");
					} else if (edge instanceof Call) {
						throw new IllegalArgumentException(
								"Procedure calls not" + " supported by concurrent trace abstraction");
					} else if (edge instanceof Return) {
						throw new IllegalArgumentException(
								"Procedure calls not" + " supported by concurrent trace abstraction");
					} else if (edge instanceof CodeBlock) {
						internalAlphabet.add((CodeBlock) edge);
					} else {
						throw new IllegalArgumentException("unknown type of edge");
					}
				}
			}
		}
		
		mLogger.debug("Step: construct the automaton");
		// construct the automaton
		final NestedWordAutomaton<CodeBlock, IPredicate> nwa =
				new NestedWordAutomaton<>(new AutomataLibraryServices(mServices), internalAlphabet, callAlphabet,
						returnAlphabet, mContentFactory);
		
		IPredicate procedureInitialState = null;
		
		mLogger.debug("Step: add states");
		final Map<BoogieIcfgLocation, IPredicate> nodes2States = new HashMap<>();
		// add states
		for (final BoogieIcfgLocation locNode : allNodes) {
			final boolean isErrorLocation = locNode.isErrorLocation();
			final Term trueTerm = mCsToolkit.getManagedScript().getScript().term("true");
			final IPredicate automatonState = mPredicateFactory.newSPredicate(locNode, trueTerm);
			nwa.addState(false, isErrorLocation, automatonState);
			nodes2States.put(locNode, automatonState);
			if (locNode == initialNode) {
				assert procedureInitialState == null : "Procedure must have" + "only one initial state";
				procedureInitialState = automatonState;
			}
			
		}
		
		mLogger.debug("Step: add transitions");
		// add transitions
		for (final BoogieIcfgLocation locNode : allNodes) {
			final IPredicate state = nodes2States.get(locNode);
			if (locNode.getOutgoingNodes() != null) {
				for (final IcfgEdge edge : locNode.getOutgoingEdges()) {
					final BoogieIcfgLocation succLoc = (BoogieIcfgLocation) edge.getTarget();
					final IPredicate succState = nodes2States.get(succLoc);
					if (edge instanceof CodeBlock) {
						final CodeBlock symbol = (CodeBlock) edge;
						nwa.addInternalTransition(state, symbol, succState);
					} else {
						throw new IllegalArgumentException("unknown type of edge");
					}
				}
			}
		}
		
		mLogger.debug("Step: SharedVarsInit part");
		final BoogieIcfgLocation entryOfInitProc = (BoogieIcfgLocation) mSharedVarsInit.getSource();
		final Term trueTerm = mCsToolkit.getManagedScript().getScript().term("true");
		final IPredicate initialContent = mPredicateFactory.newSPredicate(entryOfInitProc, trueTerm);
		nwa.addState(true, false, initialContent);
		IPredicate automatonSuccState;
		automatonSuccState = procedureInitialState;
		nwa.addInternalTransition(initialContent, mSharedVarsInit, automatonSuccState);
		
		return nwa;
	}
	
}
