/*
 * Copyright (C) 2010-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE TraceAbstraction plug-in.
 * 
 * The ULTIMATE TraceAbstraction plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE TraceAbstraction plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceAbstraction plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceAbstraction plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE TraceAbstraction plug-in grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction;

import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Procedure;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.BoogieIcfgLocation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.BoogieIcfgContainer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Summary;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.PredicateFactory;

public class CFG2NestedWordAutomaton {
	private final IUltimateServiceProvider mServices;
	
	private final CfgSmtToolkit mCsToolkit;
	private final PredicateFactory mPredicateFactory;
	private static final boolean mStoreHistory = false;
	private final boolean mInterprocedural;
	private boolean mMainMode;
	private static final String mStartProcedure = "ULTIMATE.start";
	
	private final ILogger mLogger;
	
	public CFG2NestedWordAutomaton(final IUltimateServiceProvider services, final boolean interprocedural, 
			final CfgSmtToolkit csToolkit, final PredicateFactory predicateFactory, final ILogger logger) {
		mServices = services;
		mLogger = logger;
		mCsToolkit = csToolkit;
		mPredicateFactory = predicateFactory;
		mInterprocedural = interprocedural;
	}
	
	
	/**
	 * Construct the control automata (see Trace Abstraction) for the program
	 * of rootNode.
	 * If mInterprocedural==false we construct an automaton for each procedure
	 * otherwise we construct one nested word automaton for the whole program.
	 * @param errorLoc error location of the program. If null, each state that
	 * corresponds to an error location will be accepting. Otherwise only the
	 * state corresponding to errorLoc will be accepting.
	 */
	public INestedWordAutomaton<CodeBlock,IPredicate> getNestedWordAutomaton(
							final BoogieIcfgContainer rootAnnot,
							final IStateFactory<IPredicate> tAContentFactory,
							final Collection<BoogieIcfgLocation> errorLocs) {
		final Set<BoogieIcfgLocation> initialNodes = new HashSet<BoogieIcfgLocation>();
		final Set<BoogieIcfgLocation> allNodes = new HashSet<BoogieIcfgLocation>();
		
		final Map<BoogieIcfgLocation,IPredicate> nodes2States = 
					new HashMap<BoogieIcfgLocation, IPredicate>();
		
		final Map<String, Procedure> implementations = 
			rootAnnot.getBoogieDeclarations().getProcImplementation();
		
		if (implementations.containsKey(mStartProcedure)) {
			mMainMode = true;
			mLogger.info("Mode: main mode - execution starts in main procedure");
		}
		else {
			mMainMode = false;
			mLogger.info("Mode: library - executation can start in any procedure");
		}
				
		mLogger.debug("Step: put all LocationNodes into mNodes");
		
		// put all LocationNodes into mNodes
		final LinkedList<BoogieIcfgLocation> queue = new LinkedList<BoogieIcfgLocation>();
		for (final IcfgLocation node : rootAnnot.getEntryNodes().values()) {
			final BoogieIcfgLocation locNode = (BoogieIcfgLocation) node;
			// add only LocationNodes of implementations
			final String procName = locNode.getProcedure();

			if (implementations.containsKey(procName)) {
				if (!mMainMode || procName.equals(mStartProcedure)) {
					initialNodes.add(locNode);
				}
				allNodes.add(locNode);
				queue.add(locNode);
			}
		}
		while (!queue.isEmpty()) {
			final BoogieIcfgLocation currentNode = queue.removeFirst();
			if (currentNode.getOutgoingNodes() != null) {
				for (final IcfgLocation node : currentNode.getOutgoingNodes()) {
					final BoogieIcfgLocation nextNode = (BoogieIcfgLocation) node;
					if ( !allNodes.contains(nextNode)) {
						allNodes.add(nextNode);
						queue.add(nextNode);
					}
				}
			}
		}
		
		
		mLogger.debug("Step: determine the alphabet");
		// determine the alphabet
		final Set<CodeBlock> internalAlphabet = new HashSet<CodeBlock>();
		final Set<CodeBlock> callAlphabet = new HashSet<CodeBlock>();
		final Set<CodeBlock> returnAlphabet = new HashSet<CodeBlock>();
		
		for (final BoogieIcfgLocation locNode : allNodes) {
			if (locNode.getOutgoingNodes() != null) {
				for (final IcfgEdge edge : locNode.getOutgoingEdges()) {
					if (edge instanceof Call) {
						if (mInterprocedural) {
							callAlphabet.add( ((Call) edge));
						}
					} else if (edge instanceof Return) {
						if (mInterprocedural) {
							returnAlphabet.add( 
									((Return) edge));
						}
					} else if (edge instanceof Summary) {
						final Summary summaryEdge = (Summary) edge;
						final Summary annot = summaryEdge;
						if (annot.calledProcedureHasImplementation()) {
							//do nothing if analysis is interprocedural
							//add summary otherwise
							if (!mInterprocedural) {
								internalAlphabet.add(annot);
							}
						}
						else {
							internalAlphabet.add(annot);
						}
					} else if (edge instanceof CodeBlock) {
						internalAlphabet.add(((CodeBlock) edge));
					} else {
						throw new UnsupportedOperationException("unknown edge" + edge);
					}
				}
			}
		}
		
		mLogger.debug("Step: construct the automaton");
		// construct the automaton
		final NestedWordAutomaton<CodeBlock, IPredicate> nwa =
			new NestedWordAutomaton<CodeBlock, IPredicate>(new AutomataLibraryServices(mServices), 
					internalAlphabet,
					callAlphabet,
					returnAlphabet,
					tAContentFactory);
		
		mLogger.debug("Step: add states");
		// add states
		for (final BoogieIcfgLocation locNode : allNodes) {
			final boolean isInitial = initialNodes.contains(locNode);
			final boolean isErrorLocation = errorLocs.contains(locNode);

			IPredicate automatonState;
			final Term trueTerm = mCsToolkit.getManagedScript().getScript().term("true");
			if (mStoreHistory) {
				automatonState = mPredicateFactory.newPredicateWithHistory(locNode, trueTerm, new HashMap<Integer, Term>());
			} else {
				automatonState = mPredicateFactory.newSPredicate(locNode, trueTerm); 
			}
					
			nwa.addState(isInitial, isErrorLocation, automatonState);
			nodes2States.put(locNode, automatonState);
			
//			// add transitions to the error location if correctness of the
//			// program can be violated at locNode
//			Map<AssumeStatement, TransFormula> violations = 
//					locNode.getStateAnnot().getViolations();
//			if (violations !=null) {
//				for (AssumeStatement st : violations.keySet()) {
//					TransAnnot transAnnot = new TransAnnot();
//					transAnnot.addStatement(st);
//					transAnnot.setTransitionTerm(violations.get(st));
//					internalAlphabet.add(transAnnot);
//					nwa.addInternalTransition(automatonState,transAnnot,automatonErrorState);
//				}
//			}
		}
		
		
		mLogger.debug("Step: add transitions");
		// add transitions
		for (final BoogieIcfgLocation locNode : allNodes) {
			final IPredicate state = 
				nodes2States.get(locNode);
			if (locNode.getOutgoingNodes() != null) {
				for (final IcfgEdge edge : locNode.getOutgoingEdges()) {
					final BoogieIcfgLocation succLoc = (BoogieIcfgLocation) edge.getTarget();
					final IPredicate succState = 
						nodes2States.get(succLoc); 
					if (edge instanceof Call) {
						if (mInterprocedural) {
							final CodeBlock symbol = 
									((Call) edge);
								nwa.addCallTransition(state,symbol, succState);
						}
					} else if (edge instanceof Return) {
						if (mInterprocedural) {
							final Return returnEdge = (Return) edge;
							final CodeBlock symbol = returnEdge;
							final BoogieIcfgLocation callerLocNode = returnEdge.getCallerProgramPoint();
							if (nodes2States.containsKey(callerLocNode)) {
								nwa.addReturnTransition(state,
									nodes2States.get(callerLocNode), symbol, succState);
							} else {
								mLogger.debug("Ommited insertion of " + symbol + 
										" because callerNode" + callerLocNode + " is deadcode");
							}
						}
					} else if (edge instanceof Summary) {
						final Summary summaryEdge = (Summary) edge;
						if (summaryEdge.calledProcedureHasImplementation()) {
							if (!mInterprocedural) {
								nwa.addInternalTransition(state,summaryEdge, succState);
							}
						}
						else {
							nwa.addInternalTransition(state, summaryEdge, succState);
						}
					} else if (edge instanceof CodeBlock) {
						final CodeBlock symbol = ((CodeBlock) edge);
							nwa.addInternalTransition(state,symbol, succState);
					} else {
						throw new UnsupportedOperationException("unknown edge" + edge);
					}
				}
			}
		}
		return nwa;	
	}
}
