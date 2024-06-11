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
import de.uni_freiburg.informatik.ultimate.lib.pea.Transition;
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

/**
 * This class generates the non-Stuck-At-Property condition for a given PEA.
 * 
 * 
 * @author Abigail Durst <dursta@informatik.uni-freiburg.de>
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

	// Constructor
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

	// Taken from RtInconcistencyConditionGenerator, idk what it does really
	private static Script buildSolver(final IUltimateServiceProvider services) throws AssertionError {

		SolverSettings settings = SolverBuilder.constructSolverSettings()
				.setSolverMode(SolverMode.External_ModelsAndUnsatCoreMode).setUseExternalSolver(ExternalSolver.Z3);
		if (SOLVER_LOG_DIR != null) {
			settings = settings.setDumpSmtScriptToFile(true, SOLVER_LOG_DIR, PeaViolablePhases.class.getSimpleName(),
					false);
		}
		return SolverBuilder.buildAndInitializeSolver(services, settings, "NonStuckAtPropertyConditionGenerator");
	}

	// Function which collects the set of NVPs for each PEA in the given
	// specification.
	private Map<PhaseEventAutomata, List<List<Phase>>> getNonterminalViolablePhases() {
		Map<PhaseEventAutomata, List<List<Phase>>> peaNvpMap = new HashMap<PhaseEventAutomata, List<List<Phase>>>();
		for (ReqPeas reqPeaSet : mReqPeas) {
			for (final Entry<CounterTrace, PhaseEventAutomata> pea : reqPeaSet.getCounterTrace2Pea()) {

				peaNvpMap.put(pea.getValue(), new ArrayList<>());
				PeaViolablePhases peaViolablePhases = new PeaViolablePhases(mLogger, mServices, mPeaResultUtil,
						mBoogieDeclarations, mReqSymboltable, pea.getValue());
				List<List<Phase>> phaseSets = peaViolablePhases.nonterminalPeaViolablePhases();
				List<List<Phase>> currentPeaNvps = peaNvpMap.get(pea.getValue());
				for (List<Phase> phaseSet : phaseSets) {
					currentPeaNvps.add(phaseSet);
				}
				peaNvpMap.put(pea.getValue(), currentPeaNvps);
			}
		}
		return peaNvpMap;
	}

	// Get a list of SMT statements to check for the stuck-at-property.
	// For each PEA, this is the disjunction of the following statements, for each
	// NVP:
	// program is in NVP location ==> a transition leaving the NVP can be taken
	public Map<PhaseEventAutomata, List<Expression>> generateNonStuckAtPropertyCondition() {
		Map<PhaseEventAutomata, List<Expression>> result = new HashMap<PhaseEventAutomata, List<Expression>>();
		// List<Term> tempTransitionInfo = new ArrayList<>(); // holds the disjunction
		// of the edges
		// List<Term> tempLocationInfo = new ArrayList<>(); // holds the implications of
		// the locations and edges
		List<Term> nvpPhasesPreviousLocationChecks = new ArrayList<>();
		List<Term> nvpPhasesCurrentLocationChecks = new ArrayList<>();
		// List<Term> nonNvpNextPhases = new ArrayList<>();
		Map<PhaseEventAutomata, List<List<Phase>>> nvps = getNonterminalViolablePhases();
		for (PhaseEventAutomata pea : nvps.keySet()) {
			Map<Phase, Integer> phaseIndices = getPhaseIndices(pea);
			
			// nonNvpNextPhases = new ArrayList<>();
			result.put(pea, new ArrayList<Expression>());

			for (List<Phase> nvp : nvps.get(pea)) {
				nvpPhasesPreviousLocationChecks = new ArrayList<>();
				nvpPhasesCurrentLocationChecks = new ArrayList<>();
				for (Phase p : nvp) {
					nvpPhasesPreviousLocationChecks.add(SmtUtils.binaryEquality(mScript,
							mCddToSmt.getTermVarTerm(mReqSymboltable.getHistoryVarId(mReqSymboltable.getPcName(pea))),
							mScript.numeral(Integer.toString(phaseIndices.get(p)))));
					nvpPhasesCurrentLocationChecks.add(
							SmtUtils.binaryEquality(mScript, mCddToSmt.getTermVarTerm(mReqSymboltable.getPcName(pea)),
									mScript.numeral(Integer.toString(phaseIndices.get(p)))));
				}
				Term nvpInfo = SmtUtils.implies(mScript, SmtUtils.or(mScript, nvpPhasesPreviousLocationChecks),
						SmtUtils.or(mScript, nvpPhasesCurrentLocationChecks));
				List<Expression> addResult = result.get(pea);
				addResult.add(mBoogie2Smt.getTerm2Expression().translate(nvpInfo));
				result.put(pea, addResult);
			}
		}
		return result;
	}

	private Map<Phase, Integer> getPhaseIndices(PhaseEventAutomata pea) {
		Map<Phase, Integer> phaseIdxMap = new HashMap<Phase, Integer>();

		for (int i = 0; i < pea.getPhases().length; i++) {
			phaseIdxMap.put(pea.getPhases()[i], i);
		}
		return phaseIdxMap;
	}
}
