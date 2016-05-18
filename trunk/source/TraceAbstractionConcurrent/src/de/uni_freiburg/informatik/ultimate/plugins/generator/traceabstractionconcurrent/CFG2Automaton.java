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
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.core.preferences.RcpPreferenceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.RCFGBuilder;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootAnnot;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.StatementSequence;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Summary;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.preferences.RcfgPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.preferences.RcfgPreferenceInitializer.CodeBlockSize;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;

public abstract class CFG2Automaton {

	protected final ILogger mLogger;
	protected final IUltimateServiceProvider mServices;
	
	private final RootAnnot m_RootAnnot;
	private final SmtManager m_SmtManager;
	private final StateFactory<IPredicate> m_ContentFactory;
	protected ArrayList<NestedWordAutomaton<CodeBlock, IPredicate>> m_Automata;

	private CodeBlock m_SharedVarsInit;
	private static final String m_InitProcedure = "~init";

	public CFG2Automaton(RootNode rootNode, StateFactory<IPredicate> contentFactory, SmtManager smtManager,
			IUltimateServiceProvider services) {
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(Activator.s_PLUGIN_ID);
		// m_RootNode = rootNode;
		m_RootAnnot = rootNode.getRootAnnot();
		m_ContentFactory = contentFactory;
		m_SmtManager = smtManager;
	}

	public abstract Object getResult();

	protected void constructProcedureAutomata() {

		CodeBlockSize codeBlockSize = (new RcpPreferenceProvider(RCFGBuilder.s_PLUGIN_ID)).getEnum(
				RcfgPreferenceInitializer.LABEL_CodeBlockSize, RcfgPreferenceInitializer.CodeBlockSize.class);
		if (codeBlockSize != CodeBlockSize.SingleStatement) {
			throw new IllegalArgumentException("Concurrent programs reqire" + "atomic block encoding.");
		}

		if (!m_RootAnnot.getBoogieDeclarations().getProcImplementation().containsKey(m_InitProcedure)) {
			throw new IllegalArgumentException("Concurrent program needs procedure " + m_InitProcedure
					+ " to initialize shared variables");
		}

		int numberOfProcedures;
		if (m_RootAnnot.getBoogieDeclarations().getProcImplementation().containsKey(m_InitProcedure)) {
			numberOfProcedures = m_RootAnnot.getBoogieDeclarations().getProcImplementation().size() - 1;
			mLogger.debug("Program has procedure to initialize shared variables");
		} else {
			numberOfProcedures = m_RootAnnot.getBoogieDeclarations().getProcImplementation().size();
			mLogger.debug("No procedure to initialize shared variables");
		}
		mLogger.debug("Found " + numberOfProcedures + "Procedures");

		m_Automata = new ArrayList<NestedWordAutomaton<CodeBlock, IPredicate>>(numberOfProcedures);

		m_SharedVarsInit = extractPrecondition();

		for (String proc : m_RootAnnot.getBoogieDeclarations().getProcImplementation().keySet()) {
			if (proc.equals(m_InitProcedure)) {
				continue;
			}
			ProgramPoint entry = m_RootAnnot.getEntryNodes().get(proc);
			m_Automata.add(getNestedWordAutomaton(entry));
		}
		assert (m_Automata.size() == numberOfProcedures);

	}

	private CodeBlock extractPrecondition() {
		assert (m_RootAnnot.getBoogieDeclarations().getProcImplementation().containsKey(m_InitProcedure));
		ProgramPoint entry = m_RootAnnot.getEntryNodes().get(m_InitProcedure);
		ProgramPoint exit = m_RootAnnot.getExitNodes().get(m_InitProcedure);
		List<CodeBlock> codeBlocks = new ArrayList<CodeBlock>();

		ProgramPoint current = entry;
		while (current != exit) {
			assert current.getOutgoingEdges().size() == 1;
			assert current.getOutgoingEdges().get(0) instanceof StatementSequence;
			StatementSequence succSS = (StatementSequence) current.getOutgoingEdges().get(0);
			assert succSS.getStatements().size() == 1;
			codeBlocks.add(succSS);
			current = (ProgramPoint) succSS.getTarget();
		}
		return m_RootAnnot.getCodeBlockFactory().constructSequentialComposition(entry, exit,
				true, false, codeBlocks);
	}

	/**
	 * Build NestedWordAutomaton for all code reachable from initial Node which
	 * is in the same procedure as initial Node. Initial Node does not have to
	 * be the enty Node of a procedure.
	 */
	private NestedWordAutomaton<CodeBlock, IPredicate> getNestedWordAutomaton(ProgramPoint initialNode) {

		mLogger.debug("Step: Collect all LocNodes corresponding to" + " this procedure");

		LinkedList<ProgramPoint> queue = new LinkedList<ProgramPoint>();
		Set<ProgramPoint> allNodes = new HashSet<ProgramPoint>();
		queue.add(initialNode);
		allNodes.add(initialNode);

		while (!queue.isEmpty()) {
			ProgramPoint currentNode = queue.removeFirst();

			if (currentNode.getOutgoingNodes() != null) {
				for (RCFGNode node : currentNode.getOutgoingNodes()) {
					ProgramPoint nextNode = (ProgramPoint) node;
					if (!allNodes.contains(nextNode)) {
						allNodes.add(nextNode);
						queue.add(nextNode);
					}
				}
			}
		}

		mLogger.debug("Step: determine the alphabet");
		// determine the alphabet
		Set<CodeBlock> internalAlphabet = new HashSet<CodeBlock>();
		Set<CodeBlock> callAlphabet = new HashSet<CodeBlock>(0);
		Set<CodeBlock> returnAlphabet = new HashSet<CodeBlock>(0);

		// add transAnnot from sharedVars initialization
		internalAlphabet.add(m_SharedVarsInit);

		for (ProgramPoint locNode : allNodes) {
			if (locNode.getOutgoingNodes() != null)
				for (RCFGEdge edge : locNode.getOutgoingEdges()) {
					if (edge instanceof Summary) {
						throw new IllegalArgumentException("Procedure calls not"
								+ " supported by concurrent trace abstraction");
					} else if (edge instanceof Call) {
						throw new IllegalArgumentException("Procedure calls not"
								+ " supported by concurrent trace abstraction");
					} else if (edge instanceof Return) {
						throw new IllegalArgumentException("Procedure calls not"
								+ " supported by concurrent trace abstraction");
					} else if (edge instanceof CodeBlock) {
						internalAlphabet.add((CodeBlock) edge);
					} else {
						throw new IllegalArgumentException("unknown type of edge");
					}
				}
		}

		mLogger.debug("Step: construct the automaton");
		// construct the automaton
		NestedWordAutomaton<CodeBlock, IPredicate> nwa = new NestedWordAutomaton<CodeBlock, IPredicate>(
				new AutomataLibraryServices(mServices), internalAlphabet, callAlphabet, returnAlphabet, m_ContentFactory);

		IPredicate procedureInitialState = null;

		mLogger.debug("Step: add states");
		Map<ProgramPoint, IPredicate> nodes2States = new HashMap<ProgramPoint, IPredicate>();
		// add states
		for (ProgramPoint locNode : allNodes) {
			boolean isErrorLocation = locNode.isErrorLocation();
			final Term trueTerm = m_SmtManager.getScript().term("true");
			IPredicate automatonState = m_SmtManager.getPredicateFactory().newSPredicate(locNode, trueTerm);
			nwa.addState(false, isErrorLocation, automatonState);
			nodes2States.put(locNode, automatonState);
			if (locNode == initialNode) {
				assert (procedureInitialState == null) : "Procedure must have" + "only one initial state";
				procedureInitialState = automatonState;
			}

		}

		mLogger.debug("Step: add transitions");
		// add transitions
		for (ProgramPoint locNode : allNodes) {
			IPredicate state = nodes2States.get(locNode);
			if (locNode.getOutgoingNodes() != null) {
				for (RCFGEdge edge : locNode.getOutgoingEdges()) {
					ProgramPoint succLoc = (ProgramPoint) edge.getTarget();
					IPredicate succState = nodes2States.get(succLoc);
					if (edge instanceof CodeBlock) {
						CodeBlock symbol = (CodeBlock) edge;
						nwa.addInternalTransition(state, symbol, succState);
					} else {
						throw new IllegalArgumentException("unknown type of edge");
					}
				}
			}
		}

		mLogger.debug("Step: SharedVarsInit part");
		ProgramPoint entryOfInitProc = (ProgramPoint) m_SharedVarsInit.getSource();
		final Term trueTerm = m_SmtManager.getScript().term("true");
		IPredicate initialContent = m_SmtManager.getPredicateFactory().newSPredicate(entryOfInitProc, trueTerm);
		nwa.addState(true, false, initialContent);
		IPredicate automatonSuccState;
		automatonSuccState = procedureInitialState;
		nwa.addInternalTransition(initialContent, m_SharedVarsInit, automatonSuccState);

		return nwa;
	}

}
