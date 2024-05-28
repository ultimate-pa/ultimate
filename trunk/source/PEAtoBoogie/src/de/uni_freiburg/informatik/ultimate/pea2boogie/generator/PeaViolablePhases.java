package de.uni_freiburg.informatik.ultimate.pea2boogie.generator;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;

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
 * This class generates lists of "last phases" for a given PEA.
 * 
 * It can generate lists of phases which satisfy the Nonterminal Violable Phase 
 * conditions for the Stuck-At-Property.
 * 
 * It can also generate these NVPs, but including terminal last phases. 
 * 
 * Other functions can easily be added to tweak which kind of last phase list one is interested in,
 * like perhaps excluding singular initial phases.
 *
 *
 * @author Abigail Durst <dursta@informatik.uni-freiburg.de>
 */

public class PeaViolablePhases {

	private final ILogger mLogger;
	private final PhaseEventAutomata mPea;
	private static Phase[] mAllPeaPhases;
	private static List<List<Phase>> mPowerSetPhases;
	
	// For SMT solving:
	private static final String SOLVER_LOG_DIR = null;
	private final Script mScript;
	private final ManagedScript mManagedScript;
	private final CddToSmt mCddToSmt;
	private final Boogie2SMT mBoogie2Smt;
	private final IReqSymbolTable mReqSymboltable;
	
	public PeaViolablePhases(final ILogger logger, final IUltimateServiceProvider services, final PeaResultUtil peaResultUtil, 
			final BoogieDeclarations boogieDeclarations, final IReqSymbolTable symboltable, final PhaseEventAutomata pea) {
		mPea = pea;
		mLogger = logger;
		mAllPeaPhases = mPea.getPhases();
		mPowerSetPhases = new ArrayList<>();
		
		// For SMT solving:
		mScript = buildSolver(services);
		mManagedScript = new ManagedScript(services, mScript);
		mReqSymboltable = symboltable;
		mBoogie2Smt = new Boogie2SMT(mManagedScript, boogieDeclarations, services, false);
		mCddToSmt = new CddToSmt(services, peaResultUtil, mScript, mBoogie2Smt, boogieDeclarations, mReqSymboltable);
	}
	
	// Taken from RtInconcistencyConditionGenerator, idk what it does really
	private static Script buildSolver(final IUltimateServiceProvider services) throws AssertionError {

		SolverSettings settings = SolverBuilder.constructSolverSettings()
				.setSolverMode(SolverMode.External_ModelsAndUnsatCoreMode).setUseExternalSolver(ExternalSolver.Z3);
		if (SOLVER_LOG_DIR != null) {
			settings = settings.setDumpSmtScriptToFile(true, SOLVER_LOG_DIR,
					PeaViolablePhases.class.getSimpleName(), false);
		}
		return SolverBuilder.buildAndInitializeSolver(services, settings, "PeaViolablePhases");
	}
	
	// This method generates all subsets of location of the given PEA
	// except for the empty set and the set of all locations 
	private List<List<Phase>> powerSetPeaPhases() {
        generatePowerSetPeaPhases(0, new ArrayList<>());
        return mPowerSetPhases;
    }
	
	// Helper recursive function for generating the power set
	// It doesn't have to have this much repetition, does it...? do it better
	private void generatePowerSetPeaPhases(int index, List<Phase> subsetPhases){
        if (index == mAllPeaPhases.length) {
            if (!subsetPhases.isEmpty() && subsetPhases.size() < mAllPeaPhases.length && !mPowerSetPhases.contains(subsetPhases)) {
            	List<Phase> subsetPhasesToAdd = new ArrayList<>(subsetPhases);
            	mPowerSetPhases.add(subsetPhasesToAdd);
            }
            return;
        }
        if (index < mAllPeaPhases.length) {
        	subsetPhases.add(mAllPeaPhases[index]);
        }
        generatePowerSetPeaPhases(index + 1, subsetPhases);

        subsetPhases.remove(subsetPhases.size() - 1);
        generatePowerSetPeaPhases(index + 1, subsetPhases);
        
	}
	
	// Check for each phase in a set of phases which other phases are reachable via phases of the set
	private Map<Phase, Set<Phase>> getReachabilityBetweenPhasesOfPhaseSet(final List<Phase> phaseSet){
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
	
	// Returns true for a given phase set if all phases in the set are reachable from each other
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
	
	// Checks for a given phase set if a transition can be taken given any variable and clock valuation
	private boolean outgoingTransitionsOfPhaseAreTautology(final List<Phase> phaseSet) {
		List<Term> phaseTransitionInfo = new ArrayList<>();
		for (Phase p : phaseSet) {
			for (Transition t : p.getTransitions()) {
				phaseTransitionInfo.add(SmtUtils.and(mScript, mCddToSmt.toSmt(t.getGuard()), 
						mCddToSmt.toSmt(new StrictInvariant().genStrictInv(t.getDest().getClockInvariant(), t.getResets())),  
						 mCddToSmt.toSmt(t.getDest().getStateInvariant().prime(mReqSymboltable.getConstVars()))));

			}
		}
		final LBool negationIsSat = SmtUtils.checkSatTerm(mScript, SmtUtils.not(mScript, SmtUtils.or(mScript, phaseTransitionInfo)));
		return negationIsSat == LBool.UNSAT;
	}
	
	// Removes all lists of phases from the power set which are subsets of another, leaving only maximal lists
	private List<List<Phase>> removeSubsetPhases(List<List<Phase>> setPhaseSets){
		List<List<Phase>> maxSubsets = new ArrayList<>();

        outerLoop:
        for (List<Phase> currentSet : setPhaseSets) {
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
	
	// Checks if a phase cannot become stuck due to clocks
	// First, get all clock invariants and check if their disjunction is a tautology.
	// If not, for all clock resets, add a "clock >= 0 || clock < 0" to the formula and check again
	// If it still isn't a tautology, then remove the set from the NVPs
	private boolean isTemporaryPhase(List<Phase> subsetPhase) {
		// I'm assuming this is more efficient than checking the invariants and resets at once, since most phase sets probably aren't
		// having clock issues due to some "true" clock invariant. But maybe it's better all in one sat check.
		boolean phaseSetIsTemporary = true;
		
		LBool clockInvariantsAreTautology = SmtUtils.checkSatTerm(mScript, SmtUtils.not(mScript, 
				SmtUtils.or(mScript, SmtUtils.or(mScript, getClockInvariants(subsetPhase)), 
						SmtUtils.or(mScript, getClockResetTrueFormulas(subsetPhase)))));
		// is not tautology
		if (clockInvariantsAreTautology == LBool.UNSAT) {
			phaseSetIsTemporary = false;
		}
		/*
		// this is unnecessary for many phase sets, rewrite to make more efficient
		List<String> clockResets = getPhaseSetClockResets(subsetPhase);
		
		List<String> lessThatClocks = new ArrayList<>();
		for (Phase p : subsetPhase) {
			// this assumes that the invariants are never written like "!(clock > 5.0)" 
			if (mCddToSmt.toSmt(p.getClockInvariant()).toString().indexOf("<") != -1) {
				for (String clock : mReqSymboltable.getClockVars()) {
					if (mCddToSmt.toSmt(p.getClockInvariant()).toString().indexOf(clock) != -1
							&& !clockResets.contains(clock)) {
						phaseSetIsTemporary = true;
					}
				}
			}
		}
		*/
		return phaseSetIsTemporary;
    }
	
	private List<Term> getClockInvariants(List<Phase> phaseSet){
		List<Term> clockInvariants = new ArrayList<Term>();
		for (Phase p : phaseSet) {
			clockInvariants.add(mCddToSmt.toSmt(p.getClockInvariant()));
		}
		return clockInvariants;
	}
	
	private List<Term> getClockResetTrueFormulas(List<Phase> phaseSet){
		List<Term> clockTrueFormulas = new ArrayList<Term>();
		for (Phase p : phaseSet) {
			for (Transition t : p.getTransitions()) {
				if (phaseSet.contains(t.getDest()) && t.getResets().length != 0) {
					for (String reset : t.getResets()) {
						clockTrueFormulas.add(SmtUtils.or(mScript, SmtUtils.less(mScript, 
								mCddToSmt.getTermVarTerm(reset), mScript.decimal("0.0")), 
								SmtUtils.geq(mScript,mCddToSmt.getTermVarTerm(reset), 
										mScript.decimal("0.0"))));
					}
				}
			}
		}
		return clockTrueFormulas;
	}
	
	private List<String> getPhaseSetClockResets(List<Phase> subsetPhase){
		List<String> clockResets = new ArrayList<>();
		for (Phase p : subsetPhase) {
			for (Transition t : p.getTransitions()) {
				for (String reset : t.getResets()) {
					if (subsetPhase.contains(t.getDest())) {
						clockResets.add(reset);
					}
				}
			}
		}
		return clockResets;
	}
	
	// Returns a list of phase sets (as lists) which are fulfill all SAP NVP conditions
	// except that they may be terminal.
	private List<List<Phase>> allPeaViolablePhases() {
		// Start with the power set of all the the phases of the PEA
		List<List<Phase>> violablePhases = powerSetPeaPhases();

		// Check for each set of phases if the phases are mutually reachable via phases of the set
		// and that the disjunction of their outgoing transitions are a tautology
		Iterator<List<Phase>> phaseSetIterator = violablePhases.iterator();
		while (phaseSetIterator.hasNext()) {
			List<Phase> phaseSet = phaseSetIterator.next();
			if (!phaseFulfillsSAPReachabilityCondition(phaseSet)) {
				 phaseSetIterator.remove();
			}
			else if (outgoingTransitionsOfPhaseAreTautology(phaseSet)) {
				phaseSetIterator.remove();
			}
			else if (isTemporaryPhase(phaseSet)) {
				phaseSetIterator.remove();
			}
		}
		
		// Remove all sets of phases which are subsets of others remaining
		violablePhases = removeSubsetPhases(violablePhases);
		
		
		return violablePhases;
	}
	
	// Returns a list of phase sets (as lists) which are fulfill all SAP NVP conditions
	public List<List<Phase>> nonterminalPeaViolablePhases() {
		// take the result of the function above and remove any sets which have no outgoing transition not in the set
		List<List<Phase>> violablePhases = allPeaViolablePhases();
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
		mLogger.info("The final set of NVPs for " + mPea.getName() +" is: ");
		mLogger.info(nonTerminalPhases);
		return nonTerminalPhases;
	}
}
