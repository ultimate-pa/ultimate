package de.uni_freiburg.informatik.ultimate.pea2boogie.generator;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.Stack;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.boogie.Boogie2SMT;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.boogie.BoogieDeclarations;
import de.uni_freiburg.informatik.ultimate.lib.pea.Phase;
import de.uni_freiburg.informatik.ultimate.lib.pea.PhaseEventAutomata;
import de.uni_freiburg.informatik.ultimate.lib.pea.Transition;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.solverbuilder.SolverBuilder;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.solverbuilder.SolverBuilder.ExternalSolver;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.solverbuilder.SolverBuilder.SolverMode;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.solverbuilder.SolverBuilder.SolverSettings;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.pea2boogie.CddToSmt;
import de.uni_freiburg.informatik.ultimate.pea2boogie.IReqSymbolTable;
import de.uni_freiburg.informatik.ultimate.pea2boogie.PeaResultUtil;

/**
 * This class generates a list of Nonterminal Violable Phases for a given PEA.
 * 
 *
 * @author Abigail Durst <dursta@informatik.uni-freiburg.de>
 * 
 *         TODO: restructure Tarjan function.
 * 
 *         TODO: Differentiate between lists and sets. When/why is either used? Match up variable names.
 * 
 *         TODO: Name variables/functions better for readability.
 */

public class PeaViolablePhases {

	private final ILogger mLogger;
	private final PhaseEventAutomata mPea;

	// Needed for SMT formulas:
	private static final String SOLVER_LOG_DIR = null;
	private final Script mScript;
	private final ManagedScript mManagedScript;
	private final CddToSmt mCddToSmt;
	private final Boogie2SMT mBoogie2Smt;
	private final IReqSymbolTable mReqSymbolTable;

	/**
	 * Constructor for an instance of the PeaViolablePhases class.
	 * 
	 * @param logger
	 *            TODO
	 * @param services
	 *            TODO
	 * @param peaResultUtil
	 *            TODO
	 * @param boogieDeclarations
	 *            TODO
	 * @param symbolTable
	 *            the SymbolTable containing all symbols of the PhaseEventAutomaton pea
	 * @param pea
	 *            the PhaseEventAutomaton for which the NVPs should be determined.
	 */
	public PeaViolablePhases(final ILogger logger, final IUltimateServiceProvider services,
			final PeaResultUtil peaResultUtil, final BoogieDeclarations boogieDeclarations,
			final IReqSymbolTable symbolTable, final PhaseEventAutomata pea) {
		mPea = pea;
		mLogger = logger;
		mScript = buildSolver(services);
		mManagedScript = new ManagedScript(services, mScript);
		mReqSymbolTable = symbolTable;
		mBoogie2Smt = new Boogie2SMT(mManagedScript, boogieDeclarations, services, false);
		mCddToSmt = new CddToSmt(services, peaResultUtil, mScript, mBoogie2Smt, boogieDeclarations, mReqSymbolTable);
	}

	/* Taken from RtInconcistencyConditionGenerator */
	private static Script buildSolver(final IUltimateServiceProvider services) throws AssertionError {
		SolverSettings settings = SolverBuilder.constructSolverSettings()
				.setSolverMode(SolverMode.External_ModelsAndUnsatCoreMode).setUseExternalSolver(ExternalSolver.Z3);
		if (SOLVER_LOG_DIR != null) {
			settings = settings.setDumpSmtScriptToFile(true, SOLVER_LOG_DIR, PeaViolablePhases.class.getSimpleName(),
					false);
		}
		return SolverBuilder.buildAndInitializeSolver(services, settings, "PeaViolablePhases");
	}

	/**
	 * A map is returned which maps each Phase p in the given set of Phases phaseSet to a subset of phaseSet which is
	 * reachable from p exclusively via Phases of phaseSet.
	 * 
	 * @param phaseSet
	 *            the set of Phases among which reachability should be checked.
	 * @return a map including an entry <Phase, Set<Phase>> for each Phase of phaseSet.
	 */
	private Map<Phase, Set<Phase>> getReachabilityBetweenPhasesOfPhaseSet(final List<Phase> phaseSet) {
		Map<Phase, Set<Phase>> reachabilityMap = new HashMap<Phase, Set<Phase>>();
		for (Phase p : phaseSet) {
			reachabilityMap.put(p, new HashSet<Phase>()); // Initialize map
			reachabilityMap = dfsCheckForReachabilityCheck(p, phaseSet, reachabilityMap);
		}
		return reachabilityMap;
	}

	/*
	 * old recursive version of dfsCheckForReachabilityCheck(..): private void dfsCheckForReachabilityCheck(Phase
	 * checkingPhase, Phase currentPhase, List<Phase> phaseSet, Map<Phase, Set<Phase>> reachabilityMap, Set<Phase>
	 * checked) { if (checked.contains(currentPhase)) { return; } checked.add(currentPhase); Set<Phase>
	 * currentReachablePhases = reachabilityMap.get(currentPhase); if (currentReachablePhases == null) {
	 * currentReachablePhases = new HashSet<>(); reachabilityMap.put(currentPhase, currentReachablePhases); } for
	 * (Transition t : currentPhase.getTransitions()) { Phase destPhase = t.getDest(); if (phaseSet.contains(destPhase))
	 * { currentReachablePhases.add(destPhase); dfsCheckForReachabilityCheck(checkingPhase, destPhase, phaseSet,
	 * reachabilityMap, checked); } } }
	 */

	/**
	 * From the given Phase, it is checked which Phases in the given List of Phases are reachable (via only those Phases
	 * in the given List of Phases.
	 * 
	 * @param checkingPhase
	 *            the Phase from which it is being checked which other Phases are reachable.
	 * @param phaseSet
	 *            the List of phases which are being checked for reachability from checkingPhase.
	 * @param reachabilityMap
	 *            the Map containing entries of the form <Phase, List of Phases in phaseSet which are reachable from the
	 *            Phase>
	 * @return a Map which includes entries of the form <Phase, Set of Phases which are reachable from the Phase>.
	 */
	private Map<Phase, Set<Phase>> dfsCheckForReachabilityCheck(Phase checkingPhase, List<Phase> phaseSet,
			Map<Phase, Set<Phase>> reachabilityMap) {
		Set<Phase> checked = new HashSet<Phase>();
		Stack<Phase> phaseStack = new Stack<>();
		phaseStack.push(checkingPhase);
		while (!phaseStack.isEmpty()) {
			Phase phaseOnStack = phaseStack.pop();
			if (checked.contains(phaseOnStack)) {
				continue;
			}
			checked.add(phaseOnStack);
			Set<Phase> currentReachablePhases = reachabilityMap.get(phaseOnStack);
			if (currentReachablePhases == null) {
				currentReachablePhases = new HashSet<>();
				reachabilityMap.put(phaseOnStack, currentReachablePhases);
			}
			for (Transition t : phaseOnStack.getTransitions()) {
				Phase destPhase = t.getDest();
				if (phaseSet.contains(destPhase)) {
					currentReachablePhases.add(destPhase);
					phaseStack.push(destPhase);
				}
			}
		}
		return reachabilityMap;
	}

	/**
	 * Returns True if all Phases in the given set of Phases phaseSet are strongly connected exclusively via each other.
	 * 
	 * @param phaseSet
	 *            the set of Phases to check for strong connectivity.
	 * @return True if phaseSet is strongly connected via its Phases, else False.
	 */
	private boolean phaseFulfillsSAPReachabilityCondition(final List<Phase> phaseSet) {
		Map<Phase, Set<Phase>> reachabilityMap = getReachabilityBetweenPhasesOfPhaseSet(phaseSet);
		boolean allPhasesMutuallyReachableViaPhaseSet = true;
		for (Phase p : reachabilityMap.keySet()) {
			for (Phase dest : phaseSet) {
				if (!(reachabilityMap.get(p).contains(dest))) {
					allPhasesMutuallyReachableViaPhaseSet = false;
				}
			}
		}
		return allPhasesMutuallyReachableViaPhaseSet;
	}

	/**
	 * Returns a List containing only Lists of Phases whose elements are not all contained in one of the other Lists of
	 * Phases.
	 * 
	 * @param setOfPhaseSets
	 *            the List of Lists of Phases to be sorted such that no Lists comprise a subset of Phases of another
	 *            List.
	 * @return The List of Lists of Phases in which no List comprises a subset of Phases of another List.
	 */
	private List<List<Phase>> removeSubsetPhases(List<List<Phase>> setOfPhaseSets) {
		List<List<Phase>> maxSubsets = new ArrayList<>();
		outerLoop: for (List<Phase> currentSet : setOfPhaseSets) {
			for (List<Phase> otherSet : setOfPhaseSets) {
				if (currentSet != otherSet && isSubsetPhase(currentSet, otherSet)) {
					continue outerLoop;
				}
			}
			maxSubsets.add(currentSet);
		}
		return maxSubsets;
	}

	/**
	 * Checks if the given List of Phases contains only elements of the second given List of Phases.
	 * 
	 * @param subsetPhase
	 *            the List of Phases to be checked if it is a subset of Phases of those in supersetPhase
	 * @param supersetPhase
	 *            the List of Phases to check if it contains a superset of Phases of those in subsetPhase.
	 * @return True if the Phases in subsetPhase are a subset of those in supersetPhase, else False.
	 */
	private boolean isSubsetPhase(List<Phase> subsetPhase, List<Phase> supersetPhase) {
		if (subsetPhase.size() > supersetPhase.size()) {
			return false;
		}
		return supersetPhase.containsAll(subsetPhase);
	}

	/**
	 * Checks for a given List of Phases, if some outgoing Transition can be taken given any arbitrary variable and
	 * clock valuation.
	 * 
	 * @param phaseSet
	 *            a List of Phases to be checked if all valuations satisfy some outgoing Transition from them.
	 * @return True if all variable/clock valuations satisfy some outgoing Transition from the List of Phases, else
	 *         False.
	 */
	private boolean outgoingTransitionsOfPhaseAreTautology(List<Phase> phaseSet) {
		List<Term> phaseTransitionInfo = new ArrayList<>();
		for (Phase p : phaseSet) {
			for (Transition t : p.getTransitions()) {
				phaseTransitionInfo.add(SmtUtils.and(mScript, mCddToSmt.toSmt(t.getGuard()),
						mCddToSmt.toSmt(
								new StrictInvariant().genStrictInv(t.getDest().getClockInvariant(), t.getResets())),
						mCddToSmt.toSmt(t.getDest().getStateInvariant().prime(mReqSymbolTable.getConstVars()))));
			}
		}
		final LBool negationIsSat =
				SmtUtils.checkSatTerm(mScript, SmtUtils.not(mScript, SmtUtils.or(mScript, phaseTransitionInfo)));
		return negationIsSat == LBool.UNSAT;
	}

	/**
	 * Collects all sets of strongly connected last Phases within the PhaseEventAutomaton given to the constructor. (A
	 * set of Phases is considered here to be a "last Phase", when it is violable and strongly connected.)
	 * 
	 * @return a List of Lists of Phases which are strongly connected and violable.
	 */
	private List<List<Phase>> getAllStronglyConnectedLastPhases() {
		List<List<Phase>> tarjansComponents = runTarjansAlgorithm();
		List<List<Phase>> tarjansComponentsAndSubcomponents = new ArrayList<List<Phase>>();
		for (List<Phase> phaseSet : tarjansComponents) {
			List<List<Phase>> tarjanLastPhases = getLastPhaseTarjanSubsets(phaseSet);
			for (List<Phase> lastPhase : tarjanLastPhases) {
				tarjansComponentsAndSubcomponents.add(lastPhase);
			}
		}
		return tarjansComponentsAndSubcomponents;
	}

	/**
	 * Runs Tarjan's algorithm on the PhaseEventAutomaton given to the constructor. This algorithm splits the PEA into
	 * its strongly connected components.
	 * 
	 * @return a List of Lists of Phases which make up a strongly connected component.
	 */
	private List<List<Phase>> runTarjansAlgorithm() {
		mLogger.info("PEA: " + mPea.getName());
		mLogger.info("Number of locations in PEA: " + mPea.getPhases().length);
		List<List<Phase>> tarjansComponents = new ArrayList<List<Phase>>();
		Map<Phase, Integer> indices = new HashMap<>(); // keeps track of each Phase's assigned index
		Map<Phase, Integer> lowlinks = new HashMap<>(); // keeps track of each Phase's lowlink value (see Tarjan's
														// Algorithm)
		Map<Phase, Boolean> onStack = new HashMap<>(); // keeps track of which Phases are in the SCC (in stack sccStack)
		Stack<Phase> checkedPhases = new Stack<Phase>();
		int index = 0;
		for (Phase startPhase : mPea.getPhases()) {
			if (!indices.containsKey(startPhase)) {
				Stack<Phase> checkingPhasesStack = new Stack<>(); // keeps track of which Phases are being checked
				Stack<Iterator<Transition>> transitionIteratorStack = new Stack<>();
				checkingPhasesStack.push(startPhase);
				transitionIteratorStack.push(startPhase.getTransitions().iterator());
				while (!checkingPhasesStack.isEmpty()) {
					Phase phaseOnStack = checkingPhasesStack.peek();
					Iterator<Transition> iterator = transitionIteratorStack.peek();
					if (!indices.containsKey(phaseOnStack)) {
						indices.put(phaseOnStack, index);
						lowlinks.put(phaseOnStack, index); // initial lowlink value is the same as the assigned index
						index++;
						checkedPhases.push(phaseOnStack);
						onStack.put(phaseOnStack, true);
					}
					boolean done = true;
					while (iterator.hasNext()) { // iterate through the transitions to check destination Phases
						Transition t = iterator.next();
						Phase otherPhase = t.getDest();
						if (!indices.containsKey(otherPhase)) { // if otherPhase hasn't been visited yet
							checkingPhasesStack.push(otherPhase);
							transitionIteratorStack.push(otherPhase.getTransitions().iterator());
							done = false;
							break;
						} else if (onStack.get(otherPhase)) {
							lowlinks.put(phaseOnStack, Math.min(lowlinks.get(phaseOnStack), indices.get(otherPhase)));
						}
					}
					if (done) { // save SCC on stack as SCC in the output List
						if (lowlinks.get(phaseOnStack).equals(indices.get(phaseOnStack))) {
							List<Phase> stronglyConnectedComponent = new ArrayList<>();
							Phase p;
							do {
								p = checkedPhases.pop();
								onStack.put(p, false);
								stronglyConnectedComponent.add(p);
							} while (p != phaseOnStack);
							tarjansComponents.add(stronglyConnectedComponent);
						}
						checkingPhasesStack.pop();
						transitionIteratorStack.pop();
						if (!checkingPhasesStack.isEmpty()) {
							Phase parentPhase = checkingPhasesStack.peek();
							lowlinks.put(parentPhase, Math.min(lowlinks.get(parentPhase), lowlinks.get(phaseOnStack)));
						}
					}
				}
			}
		}
		return tarjansComponents;
	}

	/*
	 * old recursive version of tarjansStronglyConnectedComponents(..): private List<List<Phase>>
	 * tarjansStronglyConnectedComponents(Phase phase, int index, Stack<Phase> checkedPhases, Map<Phase, Integer>
	 * indices, Map<Phase, Integer> lowlinks, Map<Phase, Boolean> onStack, List<List<Phase>> tarjansComponents) {
	 * indices.put(phase, index); lowlinks.put(phase, index); index++; checkedPhases.push(phase); onStack.put(phase,
	 * true); for (Transition t : phase.getTransitions()) { Phase otherPhase = t.getDest(); if
	 * (!indices.containsKey(otherPhase)) { tarjansStronglyConnectedComponents(otherPhase, index, checkedPhases,
	 * indices, lowlinks, onStack, tarjansComponents); lowlinks.put(phase, Math.min(lowlinks.get(phase),
	 * lowlinks.get(otherPhase))); } else if (onStack.get(otherPhase)) { lowlinks.put(phase,
	 * Math.min(lowlinks.get(phase), indices.get(otherPhase))); } }
	 * 
	 * List<Phase> stronglyConnectedComponent = new ArrayList<Phase>(); if (lowlinks.get(phase) == indices.get(phase)) {
	 * boolean done = false; while (!done) { Phase p = checkedPhases.pop(); onStack.put(p, false);
	 * stronglyConnectedComponent.add(p); if (p == phase) { done = true; } } } if
	 * (!stronglyConnectedComponent.isEmpty()) { tarjansComponents.add(stronglyConnectedComponent); } return
	 * tarjansComponents; }
	 */

	/**
	 * Checks a List of Phases for subsets of Phases which are last phases, i.e. set of Phases which are strongly
	 * connected, violable, and maximal.
	 * 
	 * @param phaseSet
	 *            the List of Phases to be checked for last phases.
	 * @return a List of Lists of Phases which represent last phases.
	 */
	private List<List<Phase>> getLastPhaseTarjanSubsets(List<Phase> phaseSet) {
		List<List<Phase>> allSubPhases = new ArrayList<>();
		int n = phaseSet.size();
		int count = 0;
		int numberOfSubPhases = 1 << n; // 2^n
		boolean[] phasesToCheck = new boolean[numberOfSubPhases];
		mLogger.info("check set of size: " + n);
		for (int i = numberOfSubPhases - 1; i > 0; i--) { // Iterate from largest phase set down to the smallest
			if (phasesToCheck[i])
				continue; // Don't check subsets of already detected NVPs
			List<Phase> subPhaseSet = new ArrayList<>();
			for (int j = 0; j < n; j++) {
				if ((i & (1 << j)) != 0) {
					subPhaseSet.add(phaseSet.get(j));
				}
			}
			count++;
			if (phaseFulfillsSAPReachabilityCondition(subPhaseSet)
					&& !outgoingTransitionsOfPhaseAreTautology(subPhaseSet)) {
				allSubPhases.add(subPhaseSet);
				phasesToCheck = markPhaseSubsetAsNVP(i, phasesToCheck);
				mLogger.info(count + " subsets checked");
			}
		}
		return allSubPhases;
	}

	/**
	 * Used to track which sets of Phases are to be checked and which aren't (subsets of detected NVPs should not be
	 * checked). This is done using a list of Boolean elements, each representing a Set of Phases. Given the index
	 * representing one of the Sets, the elements representing subsets of the Set are all set to False
	 * 
	 * @param setMask
	 *            the index of the element representing a Set of Phases found to be an NVP
	 * @param checkPhases
	 *            the List of Boolean elements, each of which represents a set of Phases.
	 * @return the updated List of Boolean elements, in which all elements representing subsets of the element
	 *         represented at index setMask have been changed to False.
	 */
	private boolean[] markPhaseSubsetAsNVP(int setMask, boolean[] checkPhases) {
		for (int subsetMask = setMask; subsetMask > 0; subsetMask = (subsetMask - 1) & setMask) {
			checkPhases[subsetMask] = true;
		}
		return checkPhases;
	}

	/**
	 * For the PhaseEventAutomaton given to the constructor, a list of its Nonterminal Violable Phases (NVPs) are
	 * generated. Each NVP is a List if Phases.
	 * 
	 * These Lists represent the Sets of Phases (PEA locations) which will be checked for the Stuck-At-Property.
	 * 
	 * @return a List of Lists of Phases, each of which represents an NVP of the PEA given to the constructor.
	 */
	public List<List<Phase>> nonterminalPeaViolablePhases() {
		// take the result of the function above and remove any sets which have no
		// outgoing transition not in the set
		List<List<Phase>> violablePhases = getAllStronglyConnectedLastPhases();
		violablePhases = removeSubsetPhases(violablePhases);
		List<List<Phase>> nonTerminalPhases = new ArrayList<List<Phase>>();
		for (List<Phase> subsetPhase : violablePhases) {
			for (Phase phase : subsetPhase) {
				for (Transition t : phase.getTransitions()) {
					if (!subsetPhase.contains(t.getDest()) && !nonTerminalPhases.contains(subsetPhase)) {
						nonTerminalPhases.add(subsetPhase);
					}
				}
			}
		}
		return nonTerminalPhases;
	}
}
