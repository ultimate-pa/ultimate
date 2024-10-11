package de.uni_freiburg.informatik.ultimate.pea2boogie.generator;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.boogie.Boogie2SMT;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.boogie.BoogieDeclarations;
import de.uni_freiburg.informatik.ultimate.lib.pea.CounterTrace;
import de.uni_freiburg.informatik.ultimate.lib.pea.Phase;
import de.uni_freiburg.informatik.ultimate.lib.pea.PhaseEventAutomata;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.solverbuilder.SolverBuilder;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.solverbuilder.SolverBuilder.ExternalSolver;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.solverbuilder.SolverBuilder.SolverMode;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.solverbuilder.SolverBuilder.SolverSettings;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.PatternType.ReqPeas;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.pea2boogie.CddToSmt;
import de.uni_freiburg.informatik.ultimate.pea2boogie.IReqSymbolTable;
import de.uni_freiburg.informatik.ultimate.pea2boogie.PeaResultUtil;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * This class generates the non-Stuck-At-Property condition for a given PEA.
 * 
 * 
 * @author Abigail Durst <dursta@informatik.uni-freiburg.de>
 * 
 *         TODO: Differentiate between lists and sets. When/why is either used? Match up variable names.
 * 
 *         TODO: Name variables/functions better for readability.
 */
public class NonStuckAtPropertyConditionGenerator {

	private final ILogger mLogger;
	private final List<ReqPeas> mReqPeas;

	// For SMT solving:
	private static final String SOLVER_LOG_DIR = null;
	private final Script mScript;
	private final ManagedScript mManagedScript;
	private final CddToSmt mCddToSmt;
	private final Boogie2SMT mBoogie2Smt;
	private final IReqSymbolTable mReqSymboltable;
	private final IUltimateServiceProvider mServices;
	private final PeaResultUtil mPeaResultUtil;
	private final BoogieDeclarations mBoogieDeclarations;

	/**
	 * Constructor for an instance of the NonStuckAtPropertyConditionGenerator class.
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
	 *            the IReqSymboltable containing all symbols of the given ReqPeas.
	 * @param reqPeas
	 *            the List of ReqPeas representing the set of requirements to be checked for the Stuck-At-Property.
	 */
	public NonStuckAtPropertyConditionGenerator(final ILogger logger, final IUltimateServiceProvider services,
			final PeaResultUtil peaResultUtil, final BoogieDeclarations boogieDeclarations,
			final IReqSymbolTable symboltable, final List<ReqPeas> reqPeas) {
		mReqPeas = reqPeas;
		mLogger = logger;

		// For SMT solving:
		mServices = services;
		mPeaResultUtil = peaResultUtil;
		mBoogieDeclarations = boogieDeclarations;
		mScript = buildSolver(services);
		mManagedScript = new ManagedScript(services, mScript);
		mReqSymboltable = symboltable;
		mBoogie2Smt = new Boogie2SMT(mManagedScript, boogieDeclarations, services, false);
		mCddToSmt = new CddToSmt(services, peaResultUtil, mScript, mBoogie2Smt, boogieDeclarations, mReqSymboltable);
	}

	/* Taken from RtInconcistencyConditionGenerator */
	private static Script buildSolver(final IUltimateServiceProvider services) throws AssertionError {
		SolverSettings settings = SolverBuilder.constructSolverSettings()
				.setSolverMode(SolverMode.External_ModelsAndUnsatCoreMode).setUseExternalSolver(ExternalSolver.Z3);
		if (SOLVER_LOG_DIR != null) {
			settings = settings.setDumpSmtScriptToFile(true, SOLVER_LOG_DIR, PeaViolablePhases.class.getSimpleName(),
					false);
		}
		return SolverBuilder.buildAndInitializeSolver(services, settings, "NonStuckAtPropertyConditionGenerator");
	}

	/**
	 * Returns the set of Nonterminal Violable Phases as a map for the set of requirements/PEAs given to the
	 * constructor, with an entry for each PEA of each requirement and its NVPs.
	 * 
	 * @return A Map of NVPs, whose entries have the form <PEA, NVPs of the PEA (List of Lists of Phases>.
	 */
	private Map<PhaseEventAutomata, List<List<Phase>>> getNonterminalViolablePhases() {
		Map<PhaseEventAutomata, List<List<Phase>>> peaNvpMap = new HashMap<PhaseEventAutomata, List<List<Phase>>>();
		for (ReqPeas reqPeaSet : mReqPeas) {
			peaNvpMap.putAll(getNonterminalViolablePhasesForRequirement(reqPeaSet));
		}
		return peaNvpMap;
	}

	/**
	 * Returns the set of Nonterminal Violable Phases as a Map for the given requirement, with an entry for each PEA of
	 * the requirement and its NVPs.
	 * 
	 * @return A Map of NVPs, whose entries have the form <PEA, NVPs of the PEA (List of Lists of Phases>.
	 */
	private Map<PhaseEventAutomata, List<List<Phase>>> getNonterminalViolablePhasesForRequirement(ReqPeas reqPeaSet) {
		Map<PhaseEventAutomata, List<List<Phase>>> peaNvpMap = new HashMap<PhaseEventAutomata, List<List<Phase>>>();
		for (final Entry<CounterTrace, PhaseEventAutomata> pea : reqPeaSet.getCounterTrace2Pea()) {
			peaNvpMap.put(pea.getValue(), getNonterminalViolablePhasesForPea(pea));
		}
		return peaNvpMap;
	}

	/**
	 * Returns the set of Nonterminal Violable Phases as a List for the given PEA, of which each element is a List of
	 * Phases.
	 * 
	 * @return A List of NVPs, each of which is a List of Phases.
	 */
	private List<List<Phase>> getNonterminalViolablePhasesForPea(Entry<CounterTrace, PhaseEventAutomata> pea) {
		List<List<Phase>> nvps = new ArrayList<List<Phase>>();
		PeaViolablePhases peaViolablePhases = new PeaViolablePhases(mLogger, mServices, mPeaResultUtil,
				mBoogieDeclarations, mReqSymboltable, pea.getValue());
		List<List<Phase>> phaseSets = peaViolablePhases.nonterminalPeaViolablePhases();
		for (List<Phase> phaseSet : phaseSets) {
			nvps.add(phaseSet);
		}
		return nvps;
	}

	/**
	 * Generates a list of SMT Expressions used to check for the Stuck-At-Property for each PEA in the requirement
	 * specification. For each NVP, this is a formula of the form "PEA was in NVP ==> PEA is still in NVP"
	 * 
	 * @return a Map with entries of the form <PhaseEventAutomaton, List of SMT Expressions to check for the SAP>
	 */
	public Map<PhaseEventAutomata, List<Pair<List<Phase>,Expression>>> generateNonStuckAtPropertyCondition() {
		Map<PhaseEventAutomata, List<Pair<List<Phase>,Expression>>> result = new HashMap<PhaseEventAutomata, List<Pair<List<Phase>,Expression>>>();
		Map<PhaseEventAutomata, List<List<Phase>>> nvps = getNonterminalViolablePhases();
		for (PhaseEventAutomata pea : nvps.keySet()) {
			Map<Phase, Integer> phaseIndices = getPhaseIndices(pea);
			result.put(pea, new ArrayList<Pair<List<Phase>,Expression>>());
			List<Pair<List<Phase>,Expression>> l = result.get(pea);
			for (List<Phase> nvp : nvps.get(pea)) {
				Term nvpInfo = getNonStuckAtProperyTermForNVP(nvp, phaseIndices, pea);
				Expression stuckAtCond = mBoogie2Smt.getTerm2Expression().translate(nvpInfo);
				Pair<List<Phase>,Expression> p = new Pair<List<Phase>,Expression>(nvp,stuckAtCond);
				l.add(p);
			}
			result.put(pea, l);
		}
		return result;
	}

	/**
	 * Generates the Term (the formula) representing the non-Stuck-At-Property condition for the given NVP, which is the
	 * formula whose satisfied negation indicated non-fulfillment of the SAP.
	 * 
	 * @param nvp
	 *            the Nonterminal Violable Phase (List of Phases) for which the Term should be generates
	 * @param phaseIndices
	 *            the Map which saves each Phase's index
	 * @param pea
	 *            the PhaseEventAutomaton of which the NVP is a subset
	 * @return the Term which represents the nSAPc.
	 */
	private Term getNonStuckAtProperyTermForNVP(List<Phase> nvp, Map<Phase, Integer> phaseIndices,
			PhaseEventAutomata pea) {
		List<Term> nvpPhasesPreviousLocationChecks = new ArrayList<>();
		List<Term> nvpPhasesCurrentLocationChecks = new ArrayList<>();
		for (Phase p : nvp) {
			nvpPhasesPreviousLocationChecks.add(SmtUtils.binaryEquality(mScript,
					mCddToSmt.getTermVarTerm(mReqSymboltable.getHistoryVarId(mReqSymboltable.getPcName(pea))),
					mScript.numeral(Integer.toString(phaseIndices.get(p)))));
			nvpPhasesCurrentLocationChecks
					.add(SmtUtils.binaryEquality(mScript, mCddToSmt.getTermVarTerm(mReqSymboltable.getPcName(pea)),
							mScript.numeral(Integer.toString(phaseIndices.get(p)))));
		}
		Term nvpInfo = SmtUtils.implies(mScript, SmtUtils.or(mScript, nvpPhasesPreviousLocationChecks),
				SmtUtils.or(mScript, nvpPhasesCurrentLocationChecks));
		return nvpInfo;
	}

	/**
	 * Maps each Phase of the given PEA to its index.
	 * 
	 * @param pea
	 *            the PEA whose Phases should be indexed.
	 * @return the Map containing entries of the form <Phase, index of Phase>
	 */
	private Map<Phase, Integer> getPhaseIndices(PhaseEventAutomata pea) {
		Map<Phase, Integer> phaseIdxMap = new HashMap<Phase, Integer>();
		for (int i = 0; i < pea.getPhases().length; i++) {
			phaseIdxMap.put(pea.getPhases()[i], i);
		}
		return phaseIdxMap;
	}
}
