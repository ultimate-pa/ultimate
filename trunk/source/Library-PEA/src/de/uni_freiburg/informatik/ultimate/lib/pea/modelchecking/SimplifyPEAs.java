/*
 *
 * This file is part of the PEA tool set
 *
 * The PEA tool set is a collection of tools for
 * Phase Event Automata (PEA). See
 * http://csd.informatik.uni-oldenburg.de/projects/peatools.html
 * for more information.
 *
 * Copyright (C) 2005-2006, Department for Computing Science,
 *                          University of Oldenburg
 *
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License
 * as published by the Free Software Foundation; either version 2
 * of the License, or (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301, USA
 */
package de.uni_freiburg.informatik.ultimate.lib.pea.modelchecking;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Set;

import org.apache.xerces.dom.DocumentImpl;
import org.w3c.dom.Document;
import org.w3c.dom.Element;
import org.w3c.dom.NodeList;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.lib.pea.CDD;
import de.uni_freiburg.informatik.ultimate.lib.pea.EventDecision;
import de.uni_freiburg.informatik.ultimate.lib.pea.PEANet;
import de.uni_freiburg.informatik.ultimate.lib.pea.PEATestAutomaton;
import de.uni_freiburg.informatik.ultimate.lib.pea.Phase;
import de.uni_freiburg.informatik.ultimate.lib.pea.PhaseEventAutomata;
import de.uni_freiburg.informatik.ultimate.lib.pea.RangeDecision;
import de.uni_freiburg.informatik.ultimate.lib.pea.Transition;

/**
 * Simple class that perform some methods for simplifying Phase Event Automata (PEA) and in so doing preparates the
 * automata for enabling model-checking on the output. For instance, the parallel position of the input automata is
 * computed. Additionally, it is possible to specify a file with a test formula in XML (
 * <code>pea.modelchecking.schemas.TestForm.xsd</code>), which is automatically transformed to further PEA's. They are
 * put in parallel with the remainder of the automata.
 *
 * @author Johannes Faber
 *
 */
public class SimplifyPEAs {

	public static final String VERSION = "PEA toolkit 0.9b";
	public static final String SVNVERSION = new String("$Revision: 423 $").replace("$", "");

	public static final String BADSTATESTRING = "FINAL";

	protected static final String DEFAULT_LOGGER = "SimplifyPEAs";

	protected ILogger logger;

	public SimplifyPEAs() {
		logger = ILogger.getLogger(SimplifyPEAs.DEFAULT_LOGGER);
	}

	/**
	 * This method removes all events from the given PEA.
	 *
	 * @param automaton
	 *            The events are removed directly from this automaton.
	 *
	 */
	public void removeAllEvents(final PhaseEventAutomata automaton) {
		removeEvents(automaton, null);
	}

	/**
	 * Removes event decisions with event names from a given set from a given formula. This method is called by
	 * <code>removeEvents</code>. To remove all events set events to null.
	 *
	 * @param formula
	 *            that has to be cleared from event decisions.
	 * @param events
	 *            The events to be removed. If null then all events are removed.
	 * @return the formula without event decisions.
	 */
	private CDD removeEventDecisions(final CDD formula, final Set<String> events) {
		final CDD[] children = formula.getChilds();

		if (children != null) {
			if (formula.getDecision() instanceof EventDecision
			        && (events == null || events.contains(((EventDecision) formula.getDecision()).getEvent()))) {
				final CDD formulaWithoutEvents = removeEventDecisions(children[0], events)
				        .or(removeEventDecisions(children[1], events));
				return formulaWithoutEvents;
			} else {
				final CDD[] newChildren = new CDD[children.length];
				for (int i = 0; i < children.length; i++) {
					newChildren[i] = removeEventDecisions(children[i], events);
				}
				return CDD.create(formula.getDecision(), newChildren);
			}
		}
		return formula;
	}

	/**
	 * Removes all events from a given set from a PhaseEventAutomata. If syncEvents equals null, then all events are
	 * removed.
	 *
	 * @param pea
	 *            The PEA which is modified by this operation - the appropriate events are removed.
	 * @param syncEvents
	 *            The events to be removed. If null then all events are removed.
	 *
	 */
	public void removeEvents(final PhaseEventAutomata pea, final Set<String> events) {
		final Phase[] phases = pea.getPhases();
		for (int i = 0; i < phases.length; i++) {
			final List<Transition> transitions = phases[i].getTransitions();
			for (final Transition transition : transitions) {
				final CDD guard = transition.getGuard();
				transition.setGuard(removeEventDecisions(guard, events));
			}
		}
	}

	/**
	 * This method checks a test automaton and marks all locations as final that always lead directly into a final
	 * location, ie. the transition guards and invariants do never block entering of the following final location. In
	 * this case, we can safely assume that the location is also a final location. The method has no further
	 * side-effects. Only the set of final location is possibly increased.
	 *
	 * Note that calling this method make usually only sense after removing all sync events, e.g., with
	 * <code>removeEvents</code>, and by this should only be called after building the parallel product of all involved
	 * PEA test automata.
	 *
	 * Also note that this method does not identify new final locations if the ARMC output files are annotated like in
	 * <code>ARMCExporter</code>: applying this method has simply no effect.
	 *
	 * @param pea
	 *            PEA where new final phases shall be identified
	 * @return new PEA with (possibly) newly identified final locations
	 */
	public PEATestAutomaton identifyImplicitFinalLocations(final PEATestAutomaton pea) {
		return this.identifyImplicitFinalLocations(pea, CDD.TRUE);
	}

	/**
	 * This method checks a test automaton and marks all locations as final that always lead directly into a final
	 * location, ie. the transition guards and invariants do never block entering of the following final location. In
	 * this case, we can safely assume that the location is also a final location. The method has no further
	 * side-effects. Only the set of final location is possibly increased.
	 *
	 * Note that calling this method make usually only sense after removing all sync events, e.g., with
	 * <code>removeEvents</code>, and by this should only be called after building the parallel product of all involved
	 * PEA test automata.
	 *
	 * Also note that this method does not identify new final locations if the ARMC output files are annotated like in
	 * <code>ARMCExporter</code>: applying this method has simply no effect.
	 *
	 * @param pea
	 *            PEA where new final phases shall be identified
	 * @param assumption
	 *            A condition that is assumed to be true when checking whether a transition to a final location can
	 *            always be taken or not. This is useful if it is known that an automaton does not contain TRUE
	 *            transitions but conditions that are always true in every run of the automaton.
	 * @return new PEA with (possibly) newly identified final locations
	 */
	public PEATestAutomaton identifyImplicitFinalLocations(final PEATestAutomaton pea, final CDD assumption) {
		final ArrayList<Phase> notVisited = new ArrayList<>(Arrays.asList(pea.getFinalPhases()));
		final Set<Phase> allFinals = new HashSet<>(Arrays.asList(pea.getFinalPhases()));

		while (!notVisited.isEmpty()) {
			final Phase finalPhase = notVisited.remove(0);
			allFinals.add(finalPhase);
			for (final Phase phase : pea.getPhases()) {
				if (allFinals.contains(phase)) {
					continue;
				}
				for (final Transition trans : phase.getTransitions()) {
					if (allFinals.contains(trans.getDest())) {
						if (trans.getGuard().assume(assumption) == CDD.TRUE
						        && trans.getDest().getStateInvariant() == CDD.TRUE
						        && trans.getDest().getClockInvariant() == CDD.TRUE) {
							notVisited.add(trans.getSrc());
						}
					}
				}
			}
		}
		return new PEATestAutomaton(pea.getName(), pea.getPhases(), pea.getInit(), pea.getClocks(), pea.getVariables(),
		        pea.getDeclarations(), allFinals.toArray(new Phase[allFinals.size()]));
	}

	/**
	 * Merges transitions in a given PEA. This is useful because the CDD datastructure enables the optimization of
	 * boolean formulas with range- and event-expressions. Hence, SimplifyPEAs merges the formulas on all transitions
	 * between two states and makes use of the CDD optimization for this formula.
	 *
	 * @param automaton
	 *            with transitions that shall be merged.
	 */
	public void mergeTransitions(final PEATestAutomaton automaton) {
		final Phase[] phases = automaton.getPhases();
		final Phase[] init = automaton.getInit();
		final Phase[] finalPhases = new Phase[automaton.getFinalPhases().length];
		final HashSet<Phase> oldInit = new HashSet<>(Arrays.asList(automaton.getInit()));
		final HashSet<Phase> oldFinals = new HashSet<>(Arrays.asList(automaton.getFinalPhases()));

		final HashMap<Phase, Phase> newPhases = new HashMap<>();

		/** Init newPhases-Map */
		int initCounter = 0, finalCounter = 0;
		for (int i = 0; i < phases.length; i++) {
			newPhases.put(phases[i], new Phase(phases[i].getName(), phases[i].getStateInvariant(),
			        phases[i].getClockInvariant(), phases[i].getStoppedClocks()));
			if (oldInit.contains(phases[i])) {
				init[initCounter++] = newPhases.get(phases[i]);
			}
			if (oldFinals.contains(phases[i])) {
				finalPhases[finalCounter++] = newPhases.get(phases[i]);
			}

		}

		for (int i = 0; i < phases.length; i++) {
			// System.out.println("in phase for" + phases[i]);
			final List<Transition> transitions = phases[i].getTransitions();
			final HashMap<Phase, ArrayList<Transition>> destinations = new HashMap<>();
			final HashMap<Transition, ArrayList<Transition>> transitionsForMerging = new HashMap<>();

			// Collect the transitions for the merging operation.
			for (final Transition transition : transitions) {
				boolean transitionsMerged = false;

				// Did we have seen the destination of this transition before?
				if (destinations.containsKey(transition.getDest())) {

					// Compare the reset-arrays.
					final ArrayList<Transition> transForDest = destinations.get(transition.getDest());
					Arrays.sort(transition.getResets());
					boolean noIdenticalArrayFound = true;
					for (final Transition tempTrans : transForDest) {
						Arrays.sort(tempTrans.getResets());
						// System.out.println("in 2. for" + tempTrans);
						if (Arrays.equals(tempTrans.getResets(), transition.getResets())) {
							if (!transitionsForMerging.containsKey(tempTrans)) {
								// System.out.println("in merge t1:" + tempTrans + "t2:" + transitions);
								final ArrayList<Transition> mergeList = new ArrayList<>();
								mergeList.add(transition);
								transitionsForMerging.put(tempTrans, mergeList);
							} else {
								if (transitionsForMerging.get(tempTrans) == null) {
									transitionsForMerging.put(tempTrans, new ArrayList<Transition>());
								}
								transitionsForMerging.get(tempTrans).add(transition);
							}
							noIdenticalArrayFound = false;
							transitionsMerged = true;
							break;
						}
					}
					if (noIdenticalArrayFound) {
						transForDest.add(transition);
					}

				} else {
					final ArrayList<Transition> transForDest = new ArrayList<>();
					transForDest.add(transition);
					destinations.put(transition.getDest(), transForDest);
				}
				if (!transitionsMerged) {
					transitionsForMerging.put(transition, null);
				}
			}

			/** Set the phase-pointer to the new phase. */
			phases[i] = newPhases.get(phases[i]);

			// merge the transitions
			if (!transitionsForMerging.isEmpty()) {

				for (final Transition masterTransition : transitionsForMerging.keySet()) {
					CDD masterGuard = masterTransition.getGuard();
					if (transitionsForMerging.get(masterTransition) != null) {
						// System.out.println("Master guard: " + masterGuard);

						for (final Transition subTransition : transitionsForMerging.get(masterTransition)) {
							// System.out.println("Sub guard: " + subTransition.getGuard());
							masterGuard = masterGuard.or(subTransition.getGuard());
							// System.out.println("Baue guard: " + masterGuard);
						}

					}
					// System.out.println("(" + phases[i]+ ")adde Transition mit Guard: " + masterGuard);
					phases[i].addTransition(newPhases.get(masterTransition.getDest()), masterGuard,
					        masterTransition.getResets());
				}

			} else {
				for (final Transition transition : transitions) {
					phases[i].addTransition(newPhases.get(transition.getDest()), transition.getGuard(),
					        transition.getResets());
				}
			}
		}
	}

	/**
	 * Deprecated. Does not work properly in the current version.
	 */
	// public void identifyImplicitBadStates(PhaseEventAutomata automaton,
	// String badstatestring) {
	// Phase[] phases = automaton.getPhases();
	// ArrayList<Phase> badStatePhases = new ArrayList<Phase>();
	// for (int i = 0; i < phases.length; i++) {
	// List<Transition> transitions = phases[i].getTransitions();
	// for (Transition transition : transitions) {
	// if(transition.getDest().getName().contains(badstatestring) &&
	// transition.getGuard().getDecision() instanceof EventDecision){
	// badStatePhases.add(phases[i]);
	// //phases[i].setName(phases[i].getName() + badstatestring);
	// break;
	// }
	// }
	// }
	// for (Phase phase : badStatePhases) {
	// phase.setName(phase.getName() + badstatestring);
	// }
	// }

	/**
	 * Replaces OR's in guards by two transitions. This is often needed by model-checkers like <code>Uppaal</code> or
	 * <code>ARMC</code> that do not allow arbitrary formulas on transitions.
	 *
	 * @param transition
	 *            The XML-element representing the transition with OR's.
	 * @return An ArrayList<Element> containing the XML-elements of several new transitions.
	 */
	public ArrayList<Element> eliminateORs(final Element transition) {
		final NodeList guards = transition.getElementsByTagName(XMLTags.GUARD_TAG);
		if (guards.getLength() == 0) {
			return null;
		}

		final ArrayList<Element> newTransitions = new ArrayList<>();

		final Element guard = (Element) guards.item(0);
		final NodeList resetList = transition.getElementsByTagName(XMLTags.RESET_TAG);
		final int resetCount = resetList.getLength();
		final Element formula = (Element) guard.getFirstChild();

		if (formula.getNodeName().equals(XMLTags.FORMULATREE_TAG)
		        && formula.getAttribute(XMLTags.OPERATOR_TAG).equals(XMLTags.OR_CONST)) {
			final NodeList formulaChilds = formula.getChildNodes();
			final int formulaChildCount = formulaChilds.getLength();
			for (int j = 0; j < formulaChildCount; j++) {
				final Document document = new DocumentImpl();
				final Element newTransition = (Element) document.importNode(transition, false);
				document.appendChild(newTransition);
				final Element newGuard = (Element) document.importNode(guard, false);
				final Element newFormula = (Element) document.importNode(formulaChilds.item(j), true);
				newGuard.appendChild(newFormula);
				newTransition.appendChild(newGuard);
				// Append reset nodes
				for (int i = 0; i < resetCount; i++) {
					newTransition.appendChild(document.importNode(resetList.item(i), true));
				}
				document.importNode(newTransition, true);

				newTransitions.add(newTransition);
			}
		}
		if (newTransitions.isEmpty()) {
			return null;
		}
		return newTransitions;
	}

	/**
	 * The parallel product of PEA's with test automata PEA's contains states that are marked as final or bad states.
	 * (If this states are reachable the system not safe.) In such a parallel product there are often more than one bad
	 * states. If they are not initial, then they can be merged, which is done by this method. If a final state of the
	 * original automaton has a state or a clock invariant these are moved to the entering transitions of the new bad
	 * state. This is possible since we are not interested in the automaton behaviour after entering a final state.
	 *
	 * @param automata
	 *            In this automata all bad states are merged to one single bad state.
	 * @param badstatestring
	 *            The name of the newly created bad state.
	 */
	public PEATestAutomaton mergeFinalLocations(final PEATestAutomaton automaton, final String badstatestring) {
		if (automaton.getFinalPhases() == null || automaton.getFinalPhases().length == 0) {
			return automaton;
		}

		// automaton.dump();

		final Phase[] phases = automaton.getPhases();
		final Phase badState = new Phase(badstatestring);
		// Phase[] newFinalPhases = {badState};
		final List<Phase> newInit = new ArrayList<>();
		final ArrayList<Phase> newPhases = new ArrayList<>();
		final ArrayList<Phase> newFinalPhases = new ArrayList<>();
		final Set<Phase> initPhases = new HashSet<>(Arrays.asList(automaton.getInit()));
		final HashSet<Phase> finalPhases = automaton.getFinalPhases() != null
		        ? new HashSet<>(Arrays.asList(automaton.getFinalPhases())) : null;

		// Maps the old phases to new phases.
		final HashMap<Phase, Phase> oldnewPhases = new HashMap<>();

		/* fill oldnewPhases map */
		boolean foundBadState = false;
		for (int i = 0; i < phases.length; i++) {
			if (finalPhases != null && finalPhases.contains(phases[i]) && !initPhases.contains(phases[i])) {
				oldnewPhases.put(phases[i], badState);
				if (!foundBadState) {
					newPhases.add(badState);
					newFinalPhases.add(badState);
					foundBadState = true;
				}
				// if(initList.contains(phases[i])){
				// newInit.add(badState);
				// }
			} else {
				final Phase newPhase = new Phase(phases[i].getName(), phases[i].getStateInvariant(),
				        phases[i].getClockInvariant(), phases[i].getStoppedClocks());
				newPhases.add(newPhase);
				oldnewPhases.put(phases[i], newPhase);
				if (initPhases.contains(phases[i])) {
					newInit.add(newPhase);
					/*
					 * We need to handle the special case that a phase is a final phase and it is also initial. In this
					 * case we cannot merge it because the new final phase will not have state invariants and we have no
					 * possibility to prevent that this state is entered immediately.
					 */
					if (finalPhases != null && finalPhases.contains(phases[i])) {
						newFinalPhases.add(newPhase);
					}
				}

			}
		}
		if (!foundBadState) {
			return automaton;
		}

		// Add transitions to the new states.
		for (int i = 0; i < phases.length; i++) {
			final Phase curPhase = oldnewPhases.get(phases[i]);
			if (curPhase == badState) {
				continue;
			}
			final List transitions = phases[i].getTransitions();
			for (final Iterator iter = transitions.iterator(); iter.hasNext();) {
				final Transition trans = (Transition) iter.next();
				final Phase newDest = oldnewPhases.get(trans.getDest());
				if (newDest == badState) {
					/*
					 * In this case, where the new destination is the new merged bad state, we need to ensure that the
					 * invariants of the old state do not block entering of the final state.
					 */

					/*
					 * we need to consider the clock invariants of the destination location if it is compliant with the
					 * resets
					 */
					CDD clockInv = trans.getDest().getClockInvariant();
					for (int j = 0; j < trans.getResets().length; j++) {
						final CDD clockReset = RangeDecision.create(trans.getResets()[j], RangeDecision.OP_EQ, 0);
						clockInv = clockInv.assume(clockReset);
					}

					curPhase.addTransition(newDest,
					        trans.getGuard().and(trans.getDest().getStateInvariant().prime()).and(clockInv),
					        trans.getResets());
				} else {
					curPhase.addTransition(newDest, trans.getGuard(), trans.getResets());
				}
			}
		}

		final PEATestAutomaton pta = new PEATestAutomaton(automaton.getName(),
				newPhases.toArray(new Phase[newPhases.size()]), newInit.toArray(new Phase[newInit.size()]),
				automaton.getClocks(), automaton.getVariables(), automaton.getDeclarations(),
				newFinalPhases.toArray(new Phase[newFinalPhases.size()]));

		// pta.dump();

		return pta;
	}

	/**
	 * Renames all final phases of a test automaton to badStateString.
	 *
	 * @param automata
	 *            In this automata all bad states are renamed.
	 * @param badstatestring
	 *            The bad states are named by this string.
	 *
	 */
	public void renameBadState(final PEATestAutomaton automaton, final String badstatestring) {
		for (int i = 0; i < automaton.getFinalPhases().length; i++) {
			automaton.getFinalPhases()[i].setName(badstatestring);
		}
	}

	/**
	 * The main-method applies the simplifying methods from this class to the documents gives as parameter. It reads a
	 * Phase Event Automata network and optionally a test formula, builds the parallel product for them and writes the
	 * output to an XML-file. <br>
	 *
	 * @param args
	 *            <code>Usage: input-file [formula-file] output-file [--write-ta testautomaton-file]</code><br>
	 *            <br>
	 *            <code>input-file</code> and <code>output-file</code> contain PEA's in the syntax of
	 *            <code>pea.modelchecking.schemas.PEA.xsd</code><br>
	 *            <code>formula-file</code> optionally specifies a test formula in the format of
	 *            <code>pea.modelchecking.schemas.TestForm.xsd</code><br>
	 *            <code>--write-ta testautomaton-file</code> specifies an output-file for the temporary generated test
	 *            automata.
	 */
	@SuppressWarnings("deprecation")
	public static void main(final String[] args) {
		String inputfile = null;
		String outputfile = null;
		String formulafile = null;
		String tafile = null;
		boolean tcsOutput = false;
		boolean armcOutput = false;
		boolean preserveNames = false;
		boolean mergeTrans = false;

		class ArgException extends Exception {
			private static final long serialVersionUID = 1L;
		}
		;

		try {
			if (args.length >= 2) {
				inputfile = args[args.length - 2];
				outputfile = args[args.length - 1];
				int argCounter = 0;
				while (argCounter < args.length - 2) {
					if (args[argCounter].equals("-f") || args[argCounter].equals("--formula-file")) {
						if (++argCounter >= args.length - 2) {
							throw new ArgException();
						}
						formulafile = args[argCounter++];
						continue;
					}
					if (args[argCounter].equals("-w") || args[argCounter].equals("--write-ta")) {
						if (++argCounter >= args.length - 2) {
							throw new ArgException();
						}
						tafile = args[argCounter++];
						continue;
					}
					if (args[argCounter].equals("-t") || args[argCounter].equals("--tcs")) {
						tcsOutput = true;
						argCounter++;
						continue;
					}
					if (args[argCounter].equals("-p") || args[argCounter].equals("--preserve-names")) {
						preserveNames = true;
						argCounter++;
						continue;
					}
					if (args[argCounter].equals("-m") || args[argCounter].equals("--merge-transitions")) {
						mergeTrans = true;
						argCounter++;
						continue;
					}
					if (args[argCounter].equals("-a") || args[argCounter].equals("--armc3")) {
						armcOutput = true;
						argCounter++;
						continue;
					}
					if (args[argCounter].equals("-v") || args[argCounter].equals("--version")) {
						System.out.println(VERSION);
						System.out.println(SVNVERSION);
						System.exit(0);
					}
					throw new ArgException();
				}
			} else if (args.length == 1) {
				if (args[0].equals("-v") || args[0].equals("--version")) {
					System.out.println(VERSION);
					System.out.println(SVNVERSION);
					System.exit(0);
				}
			} else {
				throw new ArgException();
			}

			// PropertyConfigurator.configure(ClassLoader.getSystemResource("pea/modelchecking/CompilerLog.config"));
			final PEAJ2XMLConverter converter = new PEAJ2XMLConverter();
			final PEAXML2JConverterWithVarList fileParser = new PEAXML2JConverterWithVarList(false);

			final SimplifyPEAs simplifier = new SimplifyPEAs();

			final PhaseEventAutomata[] peas = fileParser.convert(inputfile);
			// PhaseEventAutomata product = peas[0];
			PEATestAutomaton product = null;

			// Compile model-check formula and generate the appropriate automata.
			if (formulafile != null) {
				final Compiler compiler = new Compiler(ILogger.getLogger(SimplifyPEAs.DEFAULT_LOGGER),false);
				final ArrayList<PEATestAutomaton[]> peanetList = compiler.compile(formulafile, "");
				if (peanetList.size() > 1) {
					simplifier.logger.warn("The disjuncts in the normal form have to be checked independently.\n"
					        + "I will only check the first disjunct.");
				}

				final PEATestAutomaton[] formulaPEAs = peanetList.get(0);

				if (formulaPEAs.length > 0) {
					product = formulaPEAs[0];
				}

				if (product != null) {
					for (int i = 1; i < formulaPEAs.length; i++) {
						// identifyImplicitBadStates(formulaPEAs[i],SimplifyPEAs.BADSTATESTRING);
						simplifier.logger.info("Parallel composition with formula-pea " + i);
						product = product.parallel(formulaPEAs[i]);
					}

				}
				if (tafile != null && product != null) {
					// for (int i = 0; i < formulaPEAs.length; i++) {
					// formulaPEAs[i] = simplifier.mergeBadStates(formulaPEAs[i],SimplifyPEAs.BADSTATESTRING);
					// simplifier.renameBadState(formulaPEAs[i],SimplifyPEAs.BADSTATESTRING);
					// }
					// PEATestAutomaton[] temp = new PEATestAutomaton[1];
					// temp[0] = product;
					final ArrayList<PhaseEventAutomata> peaList = new ArrayList<>();
					peaList.add(product);
					final PEANet temp = new PEANet();
					temp.setPeas(peaList);
					converter.convert(temp, tafile);
				}
			}

			// System.out.println("***********************************\nTestautomaten:\n*****************\n");

			// product.dump();

			// System.out.println();

			// System.out.println("***********************************\nPEA:\n*****************\n");

			// for (int i = 0; i < peas.length; i++) {
			// peas[i].dump();
			// }

			// System.out.println();

			if (product == null) {
				if (peas.length < 1) {
					throw new ArgException();
				}
				product = new PEATestAutomaton(peas[0]);
				for (int i = 1; i < peas.length; i++) {
					simplifier.logger.info("Parallel composition with pea " + i);
					product = product.parallel(peas[i]);
				}

				// Debug:
				// System.out.println("Baue DEBUG-Produkt.");
				// PhaseEventAutomata product2 = peas[0];
				// for (int i = 1; i < peas.length; i++) {
				// simplifier.logger.info("Parallel composition with pea " + i);
				// product2 = product2.parallel(peas[i]);
				// }
				// product = new PEATestAutomaton(product2);
			} else {
				// Build product automaton.
				for (int i = 0; i < peas.length; i++) {
					simplifier.logger.info("Parallel composition with pea " + i);
					product = product.parallel(peas[i]);
				}
			}

			// System.out.println("***********************************\nProduct:\n*****************\n");

			// product.dump();

			// System.out.println();

			simplifier.logger.info("Parallel composition finished.");

			simplifier.logger.info("Collect variables.");
			final ArrayList[] variables = fileParser.getAdditionalVariables();
			final ArrayList[] types = fileParser.getTypes();
			// peas = new PEATestAutomaton[1];
			// peas[0] = product;
			// Merge variables to one list.
			final ArrayList<String> mergedVariables0 = new ArrayList<>();
			final ArrayList<String> mergedTypes0 = new ArrayList<>();
			final ArrayList[] mergedVariables = { mergedVariables0 };
			final ArrayList[] mergedTypes = { mergedTypes0 };
			for (int i = 0; i < variables.length; i++) {
				final Iterator typeIter = types[i].iterator();
				for (final Iterator iter = variables[i].iterator(); iter.hasNext();) {
					final String tempName = (String) iter.next();
					final String tempType = (String) typeIter.next();
					if (!mergedVariables[0].contains(tempName)) {
						mergedVariables0.add(tempName);
						mergedTypes0.add(tempType);
					}
				}
			}
			converter.setAdditionalVariables(mergedVariables);
			converter.setAdditionalTypes(mergedTypes);
			simplifier.logger.info("Finished.");

			simplifier.logger.info("Merge bad states.");
			product = simplifier.mergeFinalLocations(product, SimplifyPEAs.BADSTATESTRING);
			simplifier.logger.info("Finished.");

			// System.out.println("***********************************\nMerged Badstates:\n*****************\n");

			// product.dump();

			// System.out.println();

			simplifier.logger.info("Remove events.");
			simplifier.removeAllEvents(product);
			simplifier.logger.info("Finished.");

			// System.out.println("***********************************\nAbstracted:\n*****************\n");

			// product.dump();

			// System.out.println();

			if (mergeTrans) {
				simplifier.logger.info("Merge transitions.");
				simplifier.mergeTransitions(product);
				simplifier.logger.info("Finished.");
			}

			// System.out.println("***********************************\nMerged Trans:\n*****************\n");

			// product.dump();

			// System.out.println();

			final PEATestAutomaton[] products = { product };

			final long actTime = System.currentTimeMillis();
			if (armcOutput) {
				simplifier.logger.info("Convert formulas to DNF and output ARMC-file.");
				final PEA2ARMCConverter tcsConverter = new PEA2ARMCConverter();
				// product.dump();
				tcsConverter.convert(product, outputfile, mergedVariables0, mergedTypes0, !preserveNames);
				simplifier.logger.info("Finished.");
			} else if (tcsOutput) {
				simplifier.logger.info("Convert formulas to DNF and output TCS-file.");
				final PEA2TCSJ2XMLConverter tcsConverter = new PEA2TCSJ2XMLConverter();
				tcsConverter.setAdditionalVariables(mergedVariables);
				tcsConverter.setAdditionalTypes(mergedTypes);
				tcsConverter.convert(products, outputfile, !preserveNames);
				simplifier.logger.info("Finished.");
			} else {
				simplifier.logger.info("Convert formulas to DNF and output XML-file.");
				final List<PhaseEventAutomata> peaL = Arrays.asList((PhaseEventAutomata[]) products);
				final ArrayList<PhaseEventAutomata> peaList = new ArrayList<>(peaL);
				final PEANet peanet = new PEANet();
				peanet.setPeas(peaList);
				converter.convert(peanet, outputfile);
				simplifier.logger.info("Finished.");
			}
			System.out.println("Writing tcs representation took; " + (System.currentTimeMillis() - actTime) + " ms");

		} catch (final ArgException e) {
			System.out.println("\nUsage: java pea.modelchecking.SimplifyPEAs " + " [OPTIONS] input-file output-file\n\n"
			        + "OPTIONS:\n" + "    -f, --formula-file file     " + "Specifies an XML-file with a DC-formula.\n"
			        + "    -w, --write-ta file         " + "Specifies an additional output-file for the "
			        + "testautomaton.\n" + "    -t, --tcs                   "
			        + "Outputs TCS (XML version) instead of PEA.\n" + "    -a, --armc3                 "
			        + "Outputs TCS (ARMC3 version) instead of PEA.\n" + "    -p, --preserve-names        "
			        + "Preserves the names of the product states.\n" + "    -m, --merge-transitions     "
			        + "Tries to simplify formulae on several transitions.\n" + "                                "
			        + "May lead to smaller output but very inefficient.\n" + "    -v, --version               "
			        + "Outputs version number and terminates.\n");
		} catch (final Exception e) {
			e.printStackTrace();
		}
	}

}
