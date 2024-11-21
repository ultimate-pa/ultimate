/*
 * Copyright (C) 2010-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE TraceCheckerUtils Library.
 *
 * The ULTIMATE TraceCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TraceCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TraceCheckerUtils Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.cfg2automaton;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.function.Function;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.VpAlphabet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.BoundedPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IEmptyStackStateFactory;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.ThreadInstance;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgCallTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgForkTransitionThreadCurrent;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgForkTransitionThreadOther;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgInternalTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgJoinTransitionThreadCurrent;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgJoinTransitionThreadOther;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgReturnTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocationIterator;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.SmtFreePredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Summary;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ImmutableSet;

public class Cfg2Automaton<LETTER extends IIcfgTransition<?>> {
	private static final boolean DEBUG_STORE_HISTORY = false;

	private Cfg2Automaton() {
		// do not instantiate
	}

	/**
	 * Construct the control automata (see Trace Abstraction) for the program of rootNode. If mInterprocedural==false we
	 * construct an automaton for each procedure otherwise we construct one nested word automaton for the whole program.
	 *
	 * @param acceptingLocations
	 *            locations for which the corresponding automaton state should be accepting
	 *
	 */
	public static <LETTER> INestedWordAutomaton<LETTER, IPredicate> constructAutomatonWithSPredicates(
			final IUltimateServiceProvider services, final IIcfg<? extends IcfgLocation> icfg,
			final IEmptyStackStateFactory<IPredicate> automataStateFactory,
			final Collection<? extends IcfgLocation> acceptingLocations, final boolean interprocedural,
			final PredicateFactory predicateFactory) {
		final VpAlphabet<LETTER> vpAlphabet = extractVpAlphabet(icfg, !interprocedural);

		Function<IcfgLocation, IPredicate> predicateProvider;
		final ManagedScript mgdScript = icfg.getCfgSmtToolkit().getManagedScript();
		predicateProvider = constructSPredicateProvider(predicateFactory, mgdScript);
		final Function<IIcfgTransition<?>, LETTER> transitionMapping = constructIdentityTransitionProvider();
		return constructAutomaton(services, icfg, automataStateFactory, acceptingLocations, interprocedural, vpAlphabet,
				predicateProvider, transitionMapping);
	}

	/**
	 * @param newTransition2OldTransition
	 *            If null then this method uses the identity to map input transitions to result transitions.
	 */
	public static <LETTER> INestedWordAutomaton<LETTER, IPredicate> constructAutomatonWithDebugPredicates(
			final IUltimateServiceProvider services, final IIcfg<? extends IcfgLocation> icfg,
			final IEmptyStackStateFactory<IPredicate> automataStateFactory,
			final Collection<? extends IcfgLocation> acceptingLocations, final boolean interprocedural,
			final VpAlphabet<LETTER> vpAlphabet,
			final Map<IIcfgTransition<?>, IIcfgTransition<?>> newTransition2OldTransition) {
		final Function<IcfgLocation, IPredicate> predicateProvider = constructDebugPredicateProvider();
		final Function<IIcfgTransition<?>, LETTER> transitionMapping;
		if (newTransition2OldTransition == null) {
			transitionMapping = constructIdentityTransitionProvider();
		} else {
			transitionMapping = constructMapBasedTransitionProvider(newTransition2OldTransition);
		}
		return constructAutomaton(services, icfg, automataStateFactory, acceptingLocations, interprocedural, vpAlphabet,
				predicateProvider, transitionMapping);
	}

	public static <LETTER> BoundedPetriNet<LETTER, IPredicate> constructPetriNetWithSPredicates(
			final IUltimateServiceProvider services, final IIcfg<? extends IcfgLocation> icfg,
			final Collection<? extends IcfgLocation> acceptingLocations, final PredicateFactory predicateFactory) {
		final VpAlphabet<LETTER> vpAlphabet = extractVpAlphabet(icfg, true);

		Function<IcfgLocation, IPredicate> predicateProvider;
		final ManagedScript mgdScript = icfg.getCfgSmtToolkit().getManagedScript();
		predicateProvider = constructSPredicateProvider(predicateFactory, mgdScript);
		return constructPetriNet(services, icfg, acceptingLocations, vpAlphabet, predicateProvider, predicateFactory);
	}

	private static Function<IcfgLocation, IPredicate>
			constructSPredicateProvider(final PredicateFactory predicateFactory, final ManagedScript mgdScript) {
		Function<IcfgLocation, IPredicate> predicateProvider;
		final Term trueTerm = mgdScript.getScript().term("true");
		if (DEBUG_STORE_HISTORY) {
			predicateProvider = x -> {
				return predicateFactory.newPredicateWithHistory(x, trueTerm, new HashMap<Integer, Term>());
			};
		} else {
			predicateProvider = x -> predicateFactory.newSPredicate(x, trueTerm);
		}
		return predicateProvider;
	}

	private static Function<IcfgLocation, IPredicate> constructDebugPredicateProvider() {
		final SmtFreePredicateFactory pf = new SmtFreePredicateFactory();
		return x -> pf.newDebugPredicate(x.toString());
	}

	@SuppressWarnings("unchecked")
	private static <LETTER> Function<IIcfgTransition<?>, LETTER> constructIdentityTransitionProvider() {
		return x -> (LETTER) x;
	}

	@SuppressWarnings("unchecked")
	private static <LETTER> Function<IIcfgTransition<?>, LETTER>
			constructMapBasedTransitionProvider(final Map<IIcfgTransition<?>, IIcfgTransition<?>> mapping) {
		return x -> (LETTER) mapping.get(x);
	}

	private static <LETTER> INestedWordAutomaton<LETTER, IPredicate> constructAutomaton(
			final IUltimateServiceProvider services, final IIcfg<? extends IcfgLocation> icfg,
			final IEmptyStackStateFactory<IPredicate> automataStateFactory,
			final Collection<? extends IcfgLocation> acceptingLocations, final boolean interprocedural,
			final VpAlphabet<LETTER> vpAlphabet, final Function<IcfgLocation, IPredicate> predicateProvider,
			final Function<IIcfgTransition<?>, LETTER> letterProvider) {
		final IcfgLocationIterator<?> iter = new IcfgLocationIterator<>(icfg);
		final Set<IcfgLocation> allNodes = iter.asStream().collect(Collectors.toSet());
		final Set<? extends IcfgLocation> initialNodes = icfg.getInitialNodes();

		// construct the automaton
		final NestedWordAutomaton<LETTER, IPredicate> nwa =
				new NestedWordAutomaton<>(new AutomataLibraryServices(services), vpAlphabet, automataStateFactory);
		final Map<IcfgLocation, IPredicate> nodes2States = new HashMap<>();

		{
			// add states
			for (final IcfgLocation locNode : allNodes) {
				final boolean isInitial = initialNodes.contains(locNode);
				final boolean isAccepting = acceptingLocations.contains(locNode);
				final IPredicate automatonState = predicateProvider.apply(locNode);
				nwa.addState(isInitial, isAccepting, automatonState);
				nodes2States.put(locNode, automatonState);
			}
		}

		// add transitions
		for (final IcfgLocation locNode : allNodes) {
			final IPredicate state = nodes2States.get(locNode);
			if (locNode.getOutgoingNodes() != null) {
				for (final IcfgEdge edge : locNode.getOutgoingEdges()) {
					final IcfgLocation succLoc = edge.getTarget();
					final IPredicate succState = nodes2States.get(succLoc);
					if (edge instanceof IIcfgCallTransition<?>) {
						if (interprocedural) {
							nwa.addCallTransition(state, letterProvider.apply(edge), succState);
						}
					} else if (edge instanceof IIcfgReturnTransition<?, ?>) {
						if (interprocedural) {
							final IIcfgReturnTransition<?, ?> returnEdge = (IIcfgReturnTransition<?, ?>) edge;
							final IcfgLocation callerLocNode = returnEdge.getCallerProgramPoint();
							if (nodes2States.containsKey(callerLocNode)) {
								nwa.addReturnTransition(state, nodes2States.get(callerLocNode),
										letterProvider.apply(returnEdge), succState);
							} else {
								// did not add returnEdge because the corresponding call predecessor location is not
								// graph-reachable in the ICFG
							}
						}
					} else if (edge instanceof Summary) {
						final Summary summaryEdge = (Summary) edge;
						if (summaryEdge.calledProcedureHasImplementation()) {
							if (!interprocedural) {
								nwa.addInternalTransition(state, letterProvider.apply(summaryEdge), succState);
							}
						} else {
							nwa.addInternalTransition(state, letterProvider.apply(summaryEdge), succState);
						}
					} else if (edge instanceof IIcfgInternalTransition<?>) {
						nwa.addInternalTransition(state, letterProvider.apply(edge), succState);
					} else if (edge instanceof IIcfgForkTransitionThreadCurrent<?>) {
						throw new UnsupportedOperationException(
								"analysis for sequential programs does not support fork/join");
					} else if (edge instanceof IIcfgJoinTransitionThreadCurrent<?>) {
						throw new UnsupportedOperationException(
								"analysis for sequential programs does not support fork/join");
					} else {
						throw new UnsupportedOperationException("unsupported edge " + edge.getClass().getSimpleName());
					}
				}
			}
		}
		return nwa;
	}

	@SuppressWarnings("unchecked")
	private static <LETTER> BoundedPetriNet<LETTER, IPredicate> constructPetriNet(
			final IUltimateServiceProvider services, final IIcfg<? extends IcfgLocation> icfg,
			final Collection<? extends IcfgLocation> acceptingLocations, final VpAlphabet<LETTER> vpAlphabet,
			final Function<IcfgLocation, IPredicate> predicateProvider, final PredicateFactory predicateFactory) {
		final IcfgLocationIterator<?> iter = new IcfgLocationIterator<>(icfg);
		final Set<IcfgLocation> allNodes = iter.asStream().collect(Collectors.toSet());
		final Set<? extends IcfgLocation> initialNodes = icfg.getInitialNodes();

		// construct the net
		final BoundedPetriNet<LETTER, IPredicate> net =
				new BoundedPetriNet<>(new AutomataLibraryServices(services), vpAlphabet.getInternalAlphabet(), false);
		final Map<IcfgLocation, IPredicate> nodes2States = new HashMap<>();
		{
			// add places
			for (final IcfgLocation locNode : allNodes) {
				final boolean isInitial = initialNodes.contains(locNode);
				final boolean isAccepting = acceptingLocations.contains(locNode);
				final IPredicate place = predicateProvider.apply(locNode);
				final boolean newlyAdded = net.addPlace(place, isInitial, isAccepting);
				if (!newlyAdded) {
					throw new AssertionError("Must not add place twice: " + place);
				}
				nodes2States.put(locNode, place);
			}
		}

		final Map<IIcfgForkTransitionThreadCurrent<IcfgLocation>, List<IPredicate>> fork2notinUseState =
				new HashMap<>();
		final Map<IIcfgForkTransitionThreadCurrent<IcfgLocation>, List<IPredicate>> fork2inUseState = new HashMap<>();
		final Map<String, IPredicate> threadInstance2notinUseState = new HashMap<>();
		final Map<String, IPredicate> threadInstance2inUseState = new HashMap<>();
		final Map<LETTER, IIcfgForkTransitionThreadCurrent<IcfgLocation>> errorEdge2fork = new HashMap<>();
		{
			for (final Entry<IIcfgForkTransitionThreadCurrent<IcfgLocation>, List<ThreadInstance>> entry : icfg
					.getCfgSmtToolkit().getConcurrencyInformation().getThreadInstanceMap().entrySet()) {

				final ManagedScript mgdScript = icfg.getCfgSmtToolkit().getManagedScript();
				final Term trueTerm = mgdScript.getScript().term("true");

				final List<ThreadInstance> threadInstances = entry.getValue();
				final List<IPredicate> notinUseStates = new ArrayList<>();
				final List<IPredicate> inUseStates = new ArrayList<>();
				for (final ThreadInstance ti : threadInstances) {
					final String threadInstanceId = ti.getThreadInstanceName();
					final IPredicate threadNotInUsePredicate = threadInstance2notinUseState.computeIfAbsent(
							threadInstanceId, x -> createThreadNotInUsePredicate(x, net, predicateFactory, trueTerm));
					final IPredicate threadInUsePredicate = threadInstance2inUseState.computeIfAbsent(threadInstanceId,
							x -> createThreadInUsePredicate(x, net, predicateFactory, trueTerm));

					notinUseStates.add(threadNotInUsePredicate);
					inUseStates.add(threadInUsePredicate);
				}
				fork2notinUseState.put(entry.getKey(), notinUseStates);
				fork2inUseState.put(entry.getKey(), inUseStates);
			}
			for (final Entry<IIcfgForkTransitionThreadCurrent<IcfgLocation>, IcfgLocation> entry : icfg
					.getCfgSmtToolkit().getConcurrencyInformation().getInUseErrorNodeMap().entrySet()) {
				errorEdge2fork.put((LETTER) getIncomingEdge(entry.getValue()), entry.getKey());
			}
		}

		// add transitions
		for (final IcfgLocation locNode : allNodes) {
			final IPredicate state = nodes2States.get(locNode);
			if (locNode.getOutgoingNodes() != null) {
				for (final IcfgEdge edge : locNode.getOutgoingEdges()) {
					final IcfgLocation succLoc = edge.getTarget();
					final IPredicate succState = nodes2States.get(succLoc);
					if (edge instanceof IIcfgInternalTransition<?>) {
						if (errorEdge2fork.containsKey(edge)) {
							final List<IPredicate> threadInUse = fork2inUseState.get(errorEdge2fork.get(edge));
							final Set<IPredicate> predecessors = new HashSet<>(threadInUse);
							predecessors.add(state);
							net.addTransition((LETTER) edge, ImmutableSet.of(predecessors),
									ImmutableSet.singleton(succState));
						} else {
							net.addTransition((LETTER) edge, ImmutableSet.singleton(state),
									ImmutableSet.singleton(succState));
						}
					} else if (edge instanceof IIcfgForkTransitionThreadCurrent) {
						// add nothing, in the Petri net we only use the IIcfgForkTransitionOtherThread
					} else if (edge instanceof IIcfgForkTransitionThreadOther) {
						final IIcfgForkTransitionThreadCurrent<?> current = ((IIcfgForkTransitionThreadOther<?>) edge)
								.getCorrespondingIIcfgForkTransitionCurrentThread();
						final IcfgLocation currentThreadLoc = current.getTarget();
						final IPredicate succCurrentThread = nodes2States.get(currentThreadLoc);
						final List<IPredicate> threadInUse = fork2inUseState.get(current);
						final List<IPredicate> threadNotInUse = fork2notinUseState.get(current);
						Set<IPredicate> predecessors;
						Set<IPredicate> successors;
						{
							final int i = getThreadInstanceNumber(current, edge.getSucceedingProcedure(),
									icfg.getCfgSmtToolkit().getConcurrencyInformation().getThreadInstanceMap());
							predecessors = new HashSet<>(Arrays.asList(state, threadNotInUse.get(i)));
							successors = new HashSet<>(Arrays.asList(succCurrentThread, succState, threadInUse.get(i)));
							for (int j = 0; j < i; j++) {
								predecessors.add(threadInUse.get(j));
								successors.add(threadInUse.get(j));
							}
						}
						net.addTransition((LETTER) edge, ImmutableSet.of(predecessors), ImmutableSet.of(successors));
					} else if (edge instanceof IIcfgJoinTransitionThreadCurrent) {
						// add nothing, in the Petri net we only use the IIcfgJoinTransitionOtherThread
					} else if (edge instanceof IIcfgJoinTransitionThreadOther) {
						final IIcfgJoinTransitionThreadCurrent<?> current = ((IIcfgJoinTransitionThreadOther<?>) edge)
								.getCorrespondingIIcfgJoinTransitionCurrentThread();
						final IcfgLocation currentThreadLoc = current.getSource();
						final IPredicate predCurrentThread = nodes2States.get(currentThreadLoc);
						// if predCurrentThread is null, the position of the join in the calling
						// thread is not reachable
						if (predCurrentThread != null) {
							Set<IPredicate> predecessors;
							Set<IPredicate> successors;
							{
								final String threadInstanceName = edge.getPrecedingProcedure();
								final IPredicate threadNotInUse = threadInstance2notinUseState.get(threadInstanceName);
								final IPredicate threadInUse = threadInstance2inUseState.get(threadInstanceName);
								predecessors = Set.of(predCurrentThread, state, threadInUse);
								successors = Set.of(succState, threadNotInUse);
							}
							net.addTransition((LETTER) edge, ImmutableSet.of(predecessors),
									ImmutableSet.of(successors));
						}
					} else if (edge instanceof IIcfgCallTransition<?>) {
						throw new UnsupportedOperationException(
								"unsupported for concurrent analysis " + edge.getClass().getSimpleName());
					} else if (edge instanceof IIcfgReturnTransition<?, ?>) {
						throw new UnsupportedOperationException(
								"unsupported for concurrent analysis " + edge.getClass().getSimpleName());
					} else if (edge instanceof Summary) {
						throw new UnsupportedOperationException(
								"unsupported for concurrent analysis " + edge.getClass().getSimpleName());
					} else {
						throw new UnsupportedOperationException(
								"unknown kind of edge " + edge.getClass().getSimpleName());
					}
				}
			}
		}
		return net;
	}

	private static IcfgEdge getIncomingEdge(final IcfgLocation location) {
		IcfgEdge result = null;
		for (final IcfgEdge edge : location.getIncomingEdges()) {
			if (edge.getSource().equals(location)) {
				continue;
			}
			if (result != null) {
				throw new UnsupportedOperationException(location + " has no unique incoming edge");
			}
			result = edge;
		}
		return result;
	}

	private static <LETTER> IPredicate createThreadNotInUsePredicate(final String threadInstanceId,
			final BoundedPetriNet<LETTER, IPredicate> net, final PredicateFactory predicateFactory,
			final Term predicateTerm) {
		// TODO (2020-09-03 Dominik) Label predicate with the string below; but use trueTerm (not dontCare).
		final String threadNotInUseString = threadInstanceId + "NotInUse";
		final IPredicate threadNotInUsePredicate = predicateFactory.newPredicate(predicateTerm);
		net.addPlace(threadNotInUsePredicate, true, false);
		return threadNotInUsePredicate;
	}

	private static <LETTER> IPredicate createThreadInUsePredicate(final String threadInstanceId,
			final BoundedPetriNet<LETTER, IPredicate> net, final PredicateFactory predicateFactory,
			final Term predicateTerm) {
		// TODO (2020-09-03 Dominik) Label predicate with the string below; but use trueTerm (not dontCare).
		final String threadInUseString = threadInstanceId + "InUse";
		final IPredicate threadInUsePredicate = predicateFactory.newPredicate(predicateTerm);
		net.addPlace(threadInUsePredicate, false, false);
		return threadInUsePredicate;
	}

	private static int getThreadInstanceNumber(final IIcfgForkTransitionThreadCurrent<?> current,
			final String threadInstanceName,
			final Map<IIcfgForkTransitionThreadCurrent<IcfgLocation>, List<ThreadInstance>> threadInstanceMap) {
		final List<ThreadInstance> threadInstances = threadInstanceMap.get(current);
		int i = 0;
		for (final ThreadInstance threadInstance : threadInstances) {
			if (threadInstance.getThreadInstanceName().equals(threadInstanceName)) {
				return i;
			}
			i++;
		}
		throw new IllegalStateException("did not find thread instance " + threadInstanceName);
	}

	/**
	 * Extract from an ICFG the alphabet that is needed for an trace abstraction-based analysis.
	 *
	 * @param icfg
	 * @param intraproceduralAnalysis
	 *            In an intraprocedural analysis we ignore call and return statements. Instead we add summary edges
	 *            between the call predecessor and the return successor. If a specification of the procedure is given,
	 *            this specification is used here. If no specification is given we use the trivial ("true")
	 *            specification.
	 * @return
	 */
	@SuppressWarnings("unchecked")
	public static <LETTER> VpAlphabet<LETTER> extractVpAlphabet(final IIcfg<? extends IcfgLocation> icfg,
			final boolean intraproceduralAnalysis) {
		final Set<LETTER> internalAlphabet = new HashSet<>();
		final Set<LETTER> callAlphabet = new HashSet<>();
		final Set<LETTER> returnAlphabet = new HashSet<>();

		final IcfgLocationIterator<?> iter = new IcfgLocationIterator<>(icfg);

		while (iter.hasNext()) {
			final IcfgLocation locNode = iter.next();
			if (locNode.getOutgoingNodes() != null) {
				for (final IcfgEdge edge : locNode.getOutgoingEdges()) {
					if (edge instanceof IIcfgInternalTransition) {
						internalAlphabet.add((LETTER) edge);
					} else if (edge instanceof IIcfgCallTransition) {
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
					} else if (edge instanceof IIcfgForkTransitionThreadCurrent) {
						// add nothing, in the Petri net we only use the IIcfgForkTransitionOtherThread
					} else if (edge instanceof IIcfgForkTransitionThreadOther) {
						internalAlphabet.add((LETTER) edge);
					} else if (edge instanceof IIcfgJoinTransitionThreadCurrent) {
						// add nothing, in the Petri net we only use the IIcfgJoinTransitionOtherThread
					} else if (edge instanceof IIcfgJoinTransitionThreadOther) {
						internalAlphabet.add((LETTER) edge);
					} else {
						throw new UnsupportedOperationException(
								"unknown kind of edge " + edge.getClass().getSimpleName());
					}
				}
			}
		}
		return new VpAlphabet<>(internalAlphabet, callAlphabet, returnAlphabet);
	}
}