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
	public List<List<Phase>> powerSetPeaPhases() {
		//mLogger.info("All phases: ");
		for (Phase p : mAllPeaPhases) {
			//mLogger.info(p);
		}
        generatePowerSetPeaPhases(0, new ArrayList<>());
        //mLogger.info("Complete powerset of phases: " + mPowerSetPhases);
        return mPowerSetPhases;
    }
	
	// Helper recursive function for generating the power set
	// It doesn't have to have this much repetition, does it...? do it better lol
	public void generatePowerSetPeaPhases(int index, List<Phase> subsetPhases){
		//mLogger.info("Checking phase: " + subsetPhases);
        if (index == mAllPeaPhases.length) {
            if (!subsetPhases.isEmpty() && subsetPhases.size() < mAllPeaPhases.length && !mPowerSetPhases.contains(subsetPhases)) {
            	List<Phase> subsetPhasesToAdd = new ArrayList<>(subsetPhases);
            	mPowerSetPhases.add(subsetPhasesToAdd);
        		//mLogger.info("Adding phase: " + subsetPhases);
            }
            return;
        }

        subsetPhases.add(mAllPeaPhases[index]);
        generatePowerSetPeaPhases(index + 1, subsetPhases);

        subsetPhases.remove(subsetPhases.size() - 1);
        generatePowerSetPeaPhases(index + 1, subsetPhases);
        
	}
	
	// Check for each phase in a set of phases which other phases are reachable via phases of the set
	public Map<Phase, Set<Phase>> getReachabilityBetweenPhasesOfPhaseSet(final List<Phase> phaseSet){
		Map<Phase, Set<Phase>> reachabilityMap = new HashMap<Phase, Set<Phase>>();
		for (Phase p : phaseSet) {
			reachabilityMap.put(p, new HashSet<Phase>()); // Initialize map
			dfsCheckForReachabilityCheck(p, p, phaseSet, reachabilityMap, new HashSet<>());
		}
        //mLogger.info("Finished reachability Map: ");
        for (Phase p : reachabilityMap.keySet()) {
        	mLogger.info(p + ": " + reachabilityMap.get(p));
        }
		return reachabilityMap;
	}
	
	// Helper function for checking the reachability between phases
	public void dfsCheckForReachabilityCheck(Phase checkingPhase, Phase currentPhase, List<Phase> phaseSet, 
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
        /*
		for (Transition t : currentPhase.getTransitions()) {
			Phase destPhase = t.getDest();
			if (phaseSet.contains(destPhase)) {
                Set<Phase> reachablePhases = reachabilityMap.get(checkingPhase);
                reachablePhases.add(destPhase);
                reachabilityMap.put(checkingPhase, reachablePhases);
                dfsCheckForReachabilityCheck(checkingPhase, destPhase, phaseSet, reachabilityMap, checked);
            }
		*/
	}
	
	// Returns true for a given phase set if all phases in the set are reachable from each other
	// via only phases within the set
	public boolean phaseFulfillsSAPReachabilityCondition(final List<Phase> phaseSet) {
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
	// CAREFUL: this is checked for the set of locations as a whole, not for a singular phase.
	// idk if there are weird things that happen when not reseting clocks?
	public boolean outgoingTransitionsOfPhaseAreTautology(final List<Phase> phaseSet) {
		//mLogger.info("Checking if edges are a tautology:");
		List<Term> phaseTransitionInfo = new ArrayList<>();
		//mLogger.info("The phase being checked is:");
		for (Phase p : phaseSet) {
			//mLogger.info(p);
			//mLogger.info("The edges being checked are:");
			for (Transition t : p.getTransitions()) {
				//mLogger.info(t);
				//mLogger.info("With guard and invariants:");
				//mLogger.info(t.getGuard());
				//mLogger.info(t.getDest().getClockInvariant());
				//mLogger.info(t.getDest().getStateInvariant().prime(mReqSymboltable.getConstVars()));
				phaseTransitionInfo.add(SmtUtils.and(mScript, mCddToSmt.toSmt(t.getGuard()), 
						mCddToSmt.toSmt(new StrictInvariant().genStrictInv(t.getDest().getClockInvariant(), t.getResets())),  
						 mCddToSmt.toSmt(t.getDest().getStateInvariant().prime(mReqSymboltable.getConstVars()))));
				//mLogger.info("List was created with each edge formula");

			}
		}
		//mLogger.info("Testing is there are unsat valuations");
		final LBool negationIsSat = SmtUtils.checkSatTerm(mScript, SmtUtils.not(mScript, SmtUtils.or(mScript, phaseTransitionInfo)));
		//mLogger.info("Testwas done.");
		return negationIsSat == LBool.UNSAT;
	}
	
	// Removes all lists of phases from the power set which are subsets of another, leaving only maximal lists
	public List<List<Phase>> removeSubsetPhases(List<List<Phase>> setPhaseSets){
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
	public boolean isSubsetPhase(List<Phase> subsetPhase, List<Phase> supersetPhase) {
        if (subsetPhase.size() > supersetPhase.size()) {
            return false;
        }
        return supersetPhase.containsAll(subsetPhase);
    }
	
	// Returns a list of phase sets (as lists) which are fulfill all SAP NVP conditions
	// except that they may be terminal.
	public List<List<Phase>> allPeaViolablePhases() {
		// Start with the power set of all the the phases of the PEA
		List<List<Phase>> violablePhases = powerSetPeaPhases();
		//mLogger.info("!!!!! get the power set.");

		// Check for each set of phases if the phases are mutually reachable via phases of the set
		// and that the disjunction of their outgoing transitions are a tautology
		//mLogger.info("!!!!! started reachability.");
		Iterator<List<Phase>> phaseSetIterator = violablePhases.iterator();
		while (phaseSetIterator.hasNext()) {
			List<Phase> phaseSet = phaseSetIterator.next();
			//mLogger.info("!!!!! getting reachability map for: " + phaseSet);
			if (!phaseFulfillsSAPReachabilityCondition(phaseSet)) {
				phaseSetIterator.remove();
				//mLogger.info("!!!!! removed a phase set: non reachable phases.");
			}
			else if (outgoingTransitionsOfPhaseAreTautology(phaseSet)) {
				phaseSetIterator.remove();
				//mLogger.info("!!!!! removed a phase set: tautology.");
			}
		}
		//mLogger.info("!!!!! checked reachability.");
		
		// Remove all sets of phases which are subsets of others remaining
		violablePhases = removeSubsetPhases(violablePhases);
		//mLogger.info("!!!!! removed subsets.");
		
		
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
		//mLogger.info("!!!!! removed non-terminal phases.");
		mLogger.info("The final set of NVPs is: ");
		mLogger.info(nonTerminalPhases);
		return nonTerminalPhases;
	}
	
	// Maybe additionally remove singular initial phases which can only ever by entered initially. 
	// because in this case, the stuck-at-p may hold, but not for some part of the requirement that was triggered
}
