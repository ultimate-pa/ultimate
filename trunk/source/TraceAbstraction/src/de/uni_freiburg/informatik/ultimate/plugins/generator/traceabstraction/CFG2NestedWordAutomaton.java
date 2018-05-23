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
import java.util.Map;
import java.util.Objects;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.VpAlphabet;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgCallTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgReturnTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocationIterator;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Summary;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.PredicateFactory;

public class CFG2NestedWordAutomaton<LETTER extends IIcfgTransition<?>> {
	private static final boolean STORE_HISTORY = false;

	private final IUltimateServiceProvider mServices;
	private final CfgSmtToolkit mCsToolkit;
	private final PredicateFactory mPredicateFactory;
	private final boolean mInterprocedural;
	private final ILogger mLogger;

	public CFG2NestedWordAutomaton(final IUltimateServiceProvider services, final boolean interprocedural,
			final CfgSmtToolkit csToolkit, final PredicateFactory predicateFactory, final ILogger logger) {
		mServices = Objects.requireNonNull(services);
		mLogger = Objects.requireNonNull(logger);
		mCsToolkit = Objects.requireNonNull(csToolkit);
		mPredicateFactory = Objects.requireNonNull(predicateFactory);
		mInterprocedural = interprocedural;
	}

	/**
	 * Construct the control automata (see Trace Abstraction) for the program of rootNode. If mInterprocedural==false we
	 * construct an automaton for each procedure otherwise we construct one nested word automaton for the whole program.
	 *
	 * @param errorLoc
	 *            error location of the program. If null, each state that corresponds to an error location will be
	 *            accepting. Otherwise only the state corresponding to errorLoc will be accepting.
	 */
	@SuppressWarnings("unchecked")
	public INestedWordAutomaton<LETTER, IPredicate> getNestedWordAutomaton(final IIcfg<? extends IcfgLocation> icfg,
			final IStateFactory<IPredicate> tAContentFactory, final Collection<? extends IcfgLocation> errorLocs) {
		if (icfg.getInitialNodes().size() == 1) {
			mLogger.info("Mode: main mode - execution starts in main procedure");
		} else {
			mLogger.info("Mode: library - executation can start in any procedure");
		}

		mLogger.debug("Step: put all LocationNodes into mNodes");
		final IcfgLocationIterator<?> iter = new IcfgLocationIterator<>(icfg);

		final Set<IcfgLocation> allNodes = iter.asStream().collect(Collectors.toSet());
		final Set<? extends IcfgLocation> initialNodes = icfg.getInitialNodes();
		final Map<IcfgLocation, IPredicate> nodes2States = new HashMap<>();
		boolean interprocedural = mInterprocedural;

		VpAlphabet<LETTER> vpAlphabet = extractVpAlphabet(icfg, !interprocedural);

		mLogger.debug("Step: construct the automaton");
		// construct the automaton
		final NestedWordAutomaton<LETTER, IPredicate> nwa =
				new NestedWordAutomaton<>(new AutomataLibraryServices(mServices),
						vpAlphabet, tAContentFactory);

		mLogger.debug("Step: add states");
		// add states
		for (final IcfgLocation locNode : allNodes) {
			final boolean isInitial = initialNodes.contains(locNode);
			final boolean isErrorLocation = errorLocs.contains(locNode);

			IPredicate automatonState;
			final Term trueTerm = mCsToolkit.getManagedScript().getScript().term("true");
			if (STORE_HISTORY) {
				automatonState =
						mPredicateFactory.newPredicateWithHistory(locNode, trueTerm, new HashMap<Integer, Term>());
			} else {
				automatonState = mPredicateFactory.newSPredicate(locNode, trueTerm);
			}

			nwa.addState(isInitial, isErrorLocation, automatonState);
			nodes2States.put(locNode, automatonState);

			// // add transitions to the error location if correctness of the
			// // program can be violated at locNode
			// Map<AssumeStatement, TransFormula> violations =
			// locNode.getStateAnnot().getViolations();
			// if (violations !=null) {
			// for (AssumeStatement st : violations.keySet()) {
			// TransAnnot transAnnot = new TransAnnot();
			// transAnnot.addStatement(st);
			// transAnnot.setTransitionTerm(violations.get(st));
			// internalAlphabet.add(transAnnot);
			// nwa.addInternalTransition(automatonState,transAnnot,automatonErrorState);
			// }
			// }
		}

		mLogger.debug("Step: add transitions");
		// add transitions
		for (final IcfgLocation locNode : allNodes) {
			final IPredicate state = nodes2States.get(locNode);
			if (locNode.getOutgoingNodes() != null) {
				for (final IcfgEdge edge : locNode.getOutgoingEdges()) {
					final IcfgLocation succLoc = edge.getTarget();
					final IPredicate succState = nodes2States.get(succLoc);
					if (edge instanceof IIcfgCallTransition<?>) {
						if (interprocedural) {
							nwa.addCallTransition(state, (LETTER) edge, succState);
						}
					} else if (edge instanceof IIcfgReturnTransition<?, ?>) {
						if (interprocedural) {
							final IIcfgReturnTransition<?, ?> returnEdge = (IIcfgReturnTransition<?, ?>) edge;
							final IcfgLocation callerLocNode = returnEdge.getCallerProgramPoint();
							if (nodes2States.containsKey(callerLocNode)) {
								nwa.addReturnTransition(state, nodes2States.get(callerLocNode), (LETTER) returnEdge,
										succState);
							} else {
								mLogger.debug("Ommited insertion of " + returnEdge + " because callerNode "
										+ callerLocNode + " is deadcode");
							}
						}
					} else if (edge instanceof Summary) {
						final Summary summaryEdge = (Summary) edge;
						if (summaryEdge.calledProcedureHasImplementation()) {
							if (!interprocedural) {
								nwa.addInternalTransition(state, (LETTER) summaryEdge, succState);
							}
						} else {
							nwa.addInternalTransition(state, (LETTER) summaryEdge, succState);
						}
					} else {
						nwa.addInternalTransition(state, (LETTER) edge, succState);
					}
				}
			}
		}
		return nwa;
	}

	/**
	 * Extract from an ICFG the alphabet that is needed for an trace
	 * abstraction-based analysis.
	 * 
	 * @param icfg
	 * @param intraproceduralAnalysis
	 *            In an intraprocedural analysis we ignore call and return
	 *            statements. Instead we add summary edges between the call
	 *            predecessor and the return successor. If a specification of the
	 *            procedure is given, this specification is used here. If no
	 *            specifiation is given we use the trivial ("true") specification.
	 * @return
	 */
	public VpAlphabet<LETTER> extractVpAlphabet(final IIcfg<? extends IcfgLocation> icfg,
			boolean intraproceduralAnalysis) {
		final Set<LETTER> internalAlphabet = new HashSet<>();
		final Set<LETTER> callAlphabet = new HashSet<>();
		final Set<LETTER> returnAlphabet = new HashSet<>();

		final IcfgLocationIterator<?> iter = new IcfgLocationIterator<>(icfg);

		while (iter.hasNext()) {
			IcfgLocation locNode = iter.next();
			if (locNode.getOutgoingNodes() != null) {
				for (final IcfgEdge edge : locNode.getOutgoingEdges()) {
					if (edge instanceof IIcfgCallTransition) {
						if (!intraproceduralAnalysis) {
							callAlphabet.add((LETTER) edge);
						}
					} else if (edge instanceof IIcfgReturnTransition) {
						if (!intraproceduralAnalysis) {
							returnAlphabet.add((LETTER) edge);
						}
					} else if (edge instanceof Summary) {
						final Summary summary = (Summary) edge;
						if (summary.calledProcedureHasImplementation()) {
							// do nothing if analysis is interprocedural
							// add summary otherwise
							if (intraproceduralAnalysis) {
								internalAlphabet.add((LETTER) summary);
							}
						} else {
							internalAlphabet.add((LETTER) summary);
						}
					} else {
						internalAlphabet.add((LETTER) edge);
					}
				}
			}
		}
		return new VpAlphabet<>(internalAlphabet, callAlphabet, returnAlphabet);
	}
}
