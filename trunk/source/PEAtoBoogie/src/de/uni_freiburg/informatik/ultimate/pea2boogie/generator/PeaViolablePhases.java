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
	private final IReqSymbolTable mReqSymboltable;

	public PeaViolablePhases(final ILogger logger, final IUltimateServiceProvider services,
			final PeaResultUtil peaResultUtil, final BoogieDeclarations boogieDeclarations,
			final IReqSymbolTable symboltable, final PhaseEventAutomata pea) {
		mPea = pea;
		mLogger = logger;

		mScript = buildSolver(services);
		mManagedScript = new ManagedScript(services, mScript);
		mReqSymboltable = symboltable;
		mBoogie2Smt = new Boogie2SMT(mManagedScript, boogieDeclarations, services, false);
		mCddToSmt = new CddToSmt(services, peaResultUtil, mScript, mBoogie2Smt, boogieDeclarations, mReqSymboltable);
	}

	// Taken from RtInconcistencyConditionGenerator
	private static Script buildSolver(final IUltimateServiceProvider services) throws AssertionError {
		SolverSettings settings = SolverBuilder.constructSolverSettings()
				.setSolverMode(SolverMode.External_ModelsAndUnsatCoreMode).setUseExternalSolver(ExternalSolver.Z3);
		if (SOLVER_LOG_DIR != null) {
			settings = settings.setDumpSmtScriptToFile(true, SOLVER_LOG_DIR, PeaViolablePhases.class.getSimpleName(),
					false);
		}
		return SolverBuilder.buildAndInitializeSolver(services, settings, "PeaViolablePhases");
	}
	
	/*
	 *  
	 */
	private Map<Phase, Set<Phase>> getReachabilityBetweenPhasesOfPhaseSet(final List<Phase> phaseSet) {
		Map<Phase, Set<Phase>> reachabilityMap = new HashMap<Phase, Set<Phase>>();
		for (Phase p : phaseSet) {
			reachabilityMap.put(p, new HashSet<Phase>()); // Initialize map
			dfsCheckForReachabilityCheck(p, p, phaseSet, reachabilityMap, new HashSet<>());
		}
		return reachabilityMap;
	}

	// Helper function for checking the reachability between phases
	private void dfsCheckForReachabilityCheck(Phase checkingPhase, Phase currentPhase, List<Phase> phaseSet,
			Map<Phase, Set<Phase>> reachabilityMap, Set<Phase> checked) {
		if (checked.contains(currentPhase)) {
			return;
		}
		checked.add(currentPhase);
		Set<Phase> currentReachablePhases = reachabilityMap.get(currentPhase);
		if (currentReachablePhases == null) {
			currentReachablePhases = new HashSet<>();
			reachabilityMap.put(currentPhase, currentReachablePhases);
		}
		for (Transition t : currentPhase.getTransitions()) {
			Phase destPhase = t.getDest();
			if (phaseSet.contains(destPhase)) {
				currentReachablePhases.add(destPhase);
				dfsCheckForReachabilityCheck(checkingPhase, destPhase, phaseSet, reachabilityMap, checked);
			}
		}
	}

	// Returns true for a given phase set if all phases in the set are reachable
	// from each other
	// via only phases within the set
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

	private List<List<Phase>> removeSubsetPhases(List<List<Phase>> setPhaseSets) {
		List<List<Phase>> maxSubsets = new ArrayList<>();

		outerLoop: for (List<Phase> currentSet : setPhaseSets) {
			for (List<Phase> otherSet : setPhaseSets) {
				if (currentSet != otherSet && isSubsetPhase(currentSet, otherSet)) {
					continue outerLoop;
				}
			}
			maxSubsets.add(currentSet);
		}
		return maxSubsets;
	}

	// Helper function for generating the list of only maximal phase sets
	private boolean isSubsetPhase(List<Phase> subsetPhase, List<Phase> supersetPhase) {
		if (subsetPhase.size() > supersetPhase.size()) {
			return false;
		}
		return supersetPhase.containsAll(subsetPhase);
	}

	// Checks for a given phase set if a transition can be taken given any variable
	// and clock valuation
	private boolean outgoingTransitionsOfPhaseAreTautology(List<Phase> phaseSet) {
		List<Term> phaseTransitionInfo = new ArrayList<>();
		for (Phase p : phaseSet) {
			for (Transition t : p.getTransitions()) {
				phaseTransitionInfo.add(SmtUtils.and(mScript, mCddToSmt.toSmt(t.getGuard()),
						mCddToSmt.toSmt(
								new StrictInvariant().genStrictInv(t.getDest().getClockInvariant(), t.getResets())),
						mCddToSmt.toSmt(t.getDest().getStateInvariant().prime(mReqSymboltable.getConstVars()))));

			}
		}
		final LBool negationIsSat = SmtUtils.checkSatTerm(mScript,
				SmtUtils.not(mScript, SmtUtils.or(mScript, phaseTransitionInfo)));
		return negationIsSat == LBool.UNSAT;
	}

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

	private List<List<Phase>> runTarjansAlgorithm() {
		mLogger.info("PEA: " + mPea.getName());
		mLogger.info("Number of locations in PEA: " + mPea.getPhases().length);
		List<List<Phase>> tarjansComponents = new ArrayList<List<Phase>>();
		int index = 0;
		Stack<Phase> checkedPhases = new Stack<Phase>();
		Map<Phase, Integer> indices = new HashMap<Phase, Integer>();
		Map<Phase, Integer> lowlinks = new HashMap<Phase, Integer>();
		Map<Phase, Boolean> onStack = new HashMap<Phase, Boolean>();
		for (Phase p : mPea.getPhases()) {
			if (!indices.containsKey(p)) {
				tarjansComponents = tarjansStronglyConnectedComponents(p, index, checkedPhases, indices, lowlinks,
						onStack, tarjansComponents);
			}
		}
		return tarjansComponents;
	}

	private List<List<Phase>> tarjansStronglyConnectedComponents(Phase phase, int index, Stack<Phase> checkedPhases,
			Map<Phase, Integer> indices, Map<Phase, Integer> lowlinks, Map<Phase, Boolean> onStack,
			List<List<Phase>> tarjansComponents) {
		indices.put(phase, index);
		lowlinks.put(phase, index);
		index++;
		checkedPhases.push(phase);
		onStack.put(phase, true);

		for (Transition t : phase.getTransitions()) {
			Phase otherPhase = t.getDest();
			if (!indices.containsKey(otherPhase)) {
				tarjansStronglyConnectedComponents(otherPhase, index, checkedPhases, indices, lowlinks, onStack,
						tarjansComponents);
				lowlinks.put(phase, Math.min(lowlinks.get(phase), lowlinks.get(otherPhase)));
			} else if (onStack.get(otherPhase)) {
				lowlinks.put(phase, Math.min(lowlinks.get(phase), indices.get(otherPhase)));
			}
		}

		List<Phase> stronglyConnectedComponent = new ArrayList<Phase>();
		if (lowlinks.get(phase) == indices.get(phase)) {
			boolean done = false;
			while (!done) {
				Phase p = checkedPhases.pop();
				onStack.put(p, false);
				stronglyConnectedComponent.add(p);
				if (p == phase) {
					done = true;
				}
			}
		}
		if (!stronglyConnectedComponent.isEmpty()) {
			tarjansComponents.add(stronglyConnectedComponent);
		}
		return tarjansComponents;
	}

	// Given a strongly connected component, get all subsets which could be last
	// phases
	private List<List<Phase>> getLastPhaseTarjanSubsets(List<Phase> phaseSet) {
		List<List<Phase>> allSubPhases = new ArrayList<>();
		int n = phaseSet.size();
		int count = 0;
		int numberOfSubPhases = 1 << n; // 2^n
		boolean[] addedPhases = new boolean[numberOfSubPhases];

		mLogger.info("check strongly connected location set of size: " + n);

		for (int i = numberOfSubPhases - 1; i > 0; i--) { // Iterate from largest phase set down
			if (addedPhases[i])
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
				markPhaseSubsetAsNVP(i, addedPhases, n);
				mLogger.info(count + " of its " + count*n + " subsets checked until NVP found (or done with no NVP found)");
			}
		}
		return allSubPhases;
	}

	// Helper function that tracks which Tarjan component subsets are detected to be
	// NVPs.
	// This is so that subsets of these sets don't have to be checked
	private void markPhaseSubsetAsNVP(int setMask, boolean[] added, int n) {
		for (int subsetMask = setMask; subsetMask > 0; subsetMask = (subsetMask - 1) & setMask) {
			added[subsetMask] = true;
		}
	}

	/*
	 * For the PEA of the class instance, generate a list of its Nonterminal Violable Phases
	 * (each of which is a list of phases)
	 * 
	 * These are the sets of phases (PEA locations) which will be checked for the Stuck-At-Property.
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
		mLogger.info("NVPs of " + mPea.getName() + ": " + nonTerminalPhases);
		return nonTerminalPhases;
	}
}
