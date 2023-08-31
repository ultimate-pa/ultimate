/*
 * Copyright (C) 2023 Tobias Wießner <tobias.wiessner@mailbox.org>
 * Copyright (C) 2023 University of Freiburg
 *
 * This file is part of the ULTIMATE PEAtoBoogie plug-in.
 *
 * The ULTIMATE PEAtoBoogie plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE PEAtoBoogie plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE PEAtoBoogie plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE PEAtoBoogie plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE PEAtoBoogie plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.pea2boogie.staterecoverability;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.function.UnaryOperator;
import java.util.stream.Collector;
import java.util.stream.Collectors;
import java.util.Set;

import javax.management.RuntimeErrorException;

import de.uni_freiburg.informatik.ultimate.boogie.DeclarationInformation;
import de.uni_freiburg.informatik.ultimate.boogie.ExpressionFactory;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssignmentStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression.Operator;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IntegerLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieType;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.DefaultLocation;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger.LogLevel;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.boogie.Boogie2SMT;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.boogie.BoogieDeclarations;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.lib.pea.BoogieBooleanExpressionDecision;
import de.uni_freiburg.informatik.ultimate.lib.pea.CDD;
import de.uni_freiburg.informatik.ultimate.lib.pea.CounterTrace;
import de.uni_freiburg.informatik.ultimate.lib.pea.Phase;
import de.uni_freiburg.informatik.ultimate.lib.pea.PhaseEventAutomata;
import de.uni_freiburg.informatik.ultimate.lib.pea.Transition;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.quantifier.QuantifierPusher;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.solverbuilder.SolverBuilder;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.solverbuilder.SolverBuilder.ExternalSolver;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.solverbuilder.SolverBuilder.SolverMode;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.solverbuilder.SolverBuilder.SolverSettings;
import de.uni_freiburg.informatik.ultimate.lib.srparse.Durations;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.PatternType;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.PatternType.ReqPeas;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.pea2boogie.CddToSmt;
import de.uni_freiburg.informatik.ultimate.pea2boogie.IReqSymbolTable;
import de.uni_freiburg.informatik.ultimate.pea2boogie.PeaResultUtil;
import de.uni_freiburg.informatik.ultimate.pea2boogie.generator.RtInconcistencyConditionGenerator;
import de.uni_freiburg.informatik.ultimate.smtinterpol.DefaultLogger;
import de.uni_freiburg.informatik.ultimate.smtinterpol.option.OptionMap;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.SMTInterpol;
import de.uni_freiburg.informatik.ultimate.util.ConstructionCache;

/**
 *
 * @author Tobias Wießner <tobias.wiessner@mailbox.org>
 *
 */

public class StateRecoverabilityGenerator {

	private IReqSymbolTable mReqSymboltable;
	private Term mPrimedInvariant;
	private Script mScript;
	private ManagedScript mManagedScript;
	private Boogie2SMT mBoogie2Smt;
	private Map<String, IProgramNonOldVar> mVars;
	private IUltimateServiceProvider mServices;
	private ILogger mLogger;
	private CddToSmt mCddToSmt;
	private PeaResultUtil mPeaResultUtil;
	private BoogieDeclarations boogieDeclarations;

	private ConstructionCache<Phase, Term> mPossibleStartLocations;

	public StateRecoverabilityGenerator() {
	}

	public StateRecoverabilityGenerator(final ILogger logger, final IUltimateServiceProvider services,
			final IReqSymbolTable symboltable) {
		mReqSymboltable = symboltable;
		mServices = services;
		mLogger = logger;

		mPeaResultUtil = new PeaResultUtil(mLogger, mServices);
		mScript = buildSolver(services);
		mManagedScript = new ManagedScript(services, mScript);

		boogieDeclarations = new BoogieDeclarations(mReqSymboltable.getDeclarations(), mLogger);
		mBoogie2Smt = new Boogie2SMT(mManagedScript, boogieDeclarations, services, false);
		mVars = mBoogie2Smt.getBoogie2SmtSymbolTable().getGlobalsMap();

		mPossibleStartLocations = new ConstructionCache<>(this::constructSearchStartLocationTerm);
		mCddToSmt = new CddToSmt(mServices, mPeaResultUtil, mScript, mBoogie2Smt, boogieDeclarations, mReqSymboltable);
	}

	public Map<StateRecoverabilityVerificationCondition, Set<PeaPhaseProgramCounter>> getRelevantLocationsFromPea(
			List<ReqPeas> reqPeasList, StateRecoverabilityVerificationConditionContainer vec) {
		Map<StateRecoverabilityVerificationCondition, Set<PeaPhaseProgramCounter>> veLocation = new HashMap<>();
		Set<ReqPeas> reqPeasSet = new HashSet<>(reqPeasList);
		Set<String> declaredConstants = new HashSet<>();
		Map<ReqPeas, Term> reqPeasTerm = new HashMap<>();

		// Create Terms for every location
		for (ReqPeas reqPeas : reqPeasList) {
			List<Entry<CounterTrace, PhaseEventAutomata>> ctPeaList = reqPeas.getCounterTrace2Pea();
			Term parallelAutomaton = generateParallelAutomatonTerm(removeReqPeas(reqPeasSet, reqPeas));
			reqPeasTerm.put(reqPeas, parallelAutomaton);
		}

		for (ReqPeas reqPea : reqPeasList) {
			List<Entry<CounterTrace, PhaseEventAutomata>> ctPeaList = reqPea.getCounterTrace2Pea();
			PatternType<?> req = reqPea.getPattern();
			for (Entry<CounterTrace, PhaseEventAutomata> entry : ctPeaList) {
				Phase[] phases = entry.getValue().getPhases();
				for (int i = 0; i < phases.length; ++i) {
					Phase phase = phases[i];
					// Check for every phase if the location can fulfill the verification expression
					// TRUE -> Do not add the phase
					// FALSE -> Add the phase
					for (StateRecoverabilityVerificationCondition ve : vec.getVerificationExpressions().values()) {
						CDD verificationConditionCcd = BoogieBooleanExpressionDecision.create(ExpressionFactory.constructUnaryExpression(
								ve.getVerificationConditionExpression().getLoc(),
								de.uni_freiburg.informatik.ultimate.boogie.ast.UnaryExpression.Operator.LOGICNEG,
								ve.getVerificationConditionExpression()));
						List<Term> invariantVeList = new ArrayList<>();

						// Compute phase invariant ⋀ opposite verification expression
						final Term termVe = mCddToSmt.toSmt(verificationConditionCcd);
						invariantVeList.add(termVe);
						final Term termLocation = mCddToSmt.toSmt(phase.getStateInvariant());
						invariantVeList.add(termLocation);

						// Find satisfiable model
						final Term termModel = SmtUtils.and(mScript, invariantVeList);

						if (SmtUtils.checkSatTerm(mScript, termModel) == LBool.SAT) {
							if (!veLocation.containsKey(ve)) {
								veLocation.put(ve, new HashSet<>());
							}

							Term possibleStartPhase =
									possibleStartPhase(phase, reqPea, reqPeasTerm.get(reqPea), termVe);

							// Declare constants for Z3
							declareConstants(mScript, possibleStartPhase, declaredConstants);

							if (SmtUtils.checkSatTerm(mScript, possibleStartPhase) == LBool.SAT) {
								veLocation.get(ve).add(new PeaPhaseProgramCounter(i, phase, entry.getValue(), req));
							}
						}
					}
				}
			}
		}
		return veLocation;
	}

	private void declareConstants(Script script, Term term, Set<String> declaredConstants) {
		Sort sort = term.getSort();
		TermVariable[] termVariables = term.getFreeVars();
		for (int i = 0; i < termVariables.length; ++i) {
			// mScript.declareFun("ENG_READY", new Sort[0], sort);
			TermVariable termVariable = termVariables[i];
			if (!declaredConstants.contains(termVariable.getName())) {
				script.declareFun(termVariable.getName(), new Sort[0], sort);
				declaredConstants.add(termVariable.getName());
			}
		}
	}

	private Term possibleStartPhase(Phase phase, ReqPeas reqPeas, Term parallelAutomaton, Term termVe) {
		Term actualTerm = generatePhaseTerm(phase);
		Term[] terms = new Term[] { actualTerm, parallelAutomaton, termVe };

		final Term finalTerm = termAnd(terms);
		return finalTerm;
	}

	private Term termAnd(Term[] terms) {
		final Term term = SmtUtils.and(mScript, terms);
		return term;
	}

	private Term generatePhaseTerm(Phase phase) {
		final Term term = mCddToSmt.toSmt(phase.getStateInvariant());
		return term;
	}

	private Set<ReqPeas> removeReqPeas(Set<ReqPeas> reqPeasSet, ReqPeas reqPeas) {
		Set<ReqPeas> newReqPeasSet = new HashSet<>(reqPeasSet);
		newReqPeasSet.remove(reqPeas);
		return newReqPeasSet;
	}

	/**
	 * Computes VE && (A_1 && A_2 && A_n && ...)
	 * 
	 * A = ((p_1 && (g_1 || g_n)) || (p_2 && (g_n)) || ...)
	 * 
	 * @param reqPeas
	 * @return term
	 */
	private Term generateParallelAutomatonTerm(Set<ReqPeas> reqPeas) {
		Map<ReqPeas, PhaseEventAutomata[]> reqPeasPeaArrayMap = createPeaArray(reqPeas);
		CDD reqsCDD = null;
		for (Map.Entry<ReqPeas, PhaseEventAutomata[]> entry : reqPeasPeaArrayMap.entrySet()) {

			// Automatons per requirement
			CDD peasCDD = null;
			PhaseEventAutomata[] peaArray = entry.getValue();
			for (PhaseEventAutomata pea : peaArray) {
				Phase[] phases = pea.getPhases();

				// Create CDD for every location and guard
				CDD[] invariantPhaseGuardArrayPerPea = new CDD[pea.getPhases().length];
				for (int i = 0; i < invariantPhaseGuardArrayPerPea.length; ++i) {
					Phase phase = phases[i];
					CDD invariantPhaseGuardCDD = phase.getStateInvariant().and(phase.getClockInvariant());
					invariantPhaseGuardArrayPerPea[i] = invariantPhaseGuardCDD;
				}

				// Link every location-guard CDD with OR
				CDD peaCDD = null;
				for (int i = 0; i < invariantPhaseGuardArrayPerPea.length; ++i) {
					if (peaCDD == null) {
						peaCDD = invariantPhaseGuardArrayPerPea[i];
					}
					peaCDD.or(invariantPhaseGuardArrayPerPea[i]);
				}

				// Link every pea with AND
				if (peasCDD == null) {
					peasCDD = peaCDD;
				} else {
					peasCDD.and(peaCDD);
				}
			}
			// Link every req with AND
			if (reqsCDD == null) {
				reqsCDD = peasCDD;
			} else {
				reqsCDD.and(peasCDD);
			}
		}
		final Term term = mCddToSmt.toSmt(reqsCDD);
		return term;
	}

	private Map<ReqPeas, PhaseEventAutomata[]> createPeaArray(Set<ReqPeas> reqPeas) {
		Map<ReqPeas, PhaseEventAutomata[]> reqPeasPeaArrayMap = new HashMap<>();
		for (ReqPeas reqPea : reqPeas) {
			List<Entry<CounterTrace, PhaseEventAutomata>> ctPeaList = reqPea.getCounterTrace2Pea();
			Set<PhaseEventAutomata> automataSet = ctPeaList.stream()
					.map(Entry<CounterTrace, PhaseEventAutomata>::getValue).collect(Collectors.toSet());
			final PhaseEventAutomata[] automata = automataSet.toArray(new PhaseEventAutomata[automataSet.size()]);
			reqPeasPeaArrayMap.put(reqPea, automata);
		}
		return reqPeasPeaArrayMap;
	}

	private Term constructSearchStartLocationTerm(Phase phase) {
		return transformAndLog(phase.getStateInvariant(), "phase invariant");
	}

	private Term transformAndLog(final CDD org, final String msg) {
		final Term term = mCddToSmt.toSmt(org);
		mLogger.info("Can be start location %s %s", msg, org.toGeneralString());
		return term;
	}

	private static Script buildSolver(final IUltimateServiceProvider services) throws AssertionError {
		SolverSettings settings = SolverBuilder.constructSolverSettings()
				// .setSolverMode(SolverMode.External_ModelsAndUnsatCoreMode).setUseExternalSolver(ExternalSolver.Z3);
				.setSolverMode(SolverMode.External_ModelsMode).setUseExternalSolver(ExternalSolver.Z3);
		return SolverBuilder.buildAndInitializeSolver(services, settings, "RtInconsistencySolver");
	}

	public Map<StateRecoverabilityVerificationCondition, Map<PhaseEventAutomata, Set<StateRecoverabilityAuxiliaryStatement>>>
			getAuxStatementPerVerificationExpression(AuxiliaryStatementContainer auxStatementContainer) {
		Map<StateRecoverabilityVerificationCondition, Map<PhaseEventAutomata, Set<StateRecoverabilityAuxiliaryStatement>>> vePeaAuxStatementMap =
				new HashMap<>();
		for (AuxiliaryStatement auxStatement : auxStatementContainer.getSreMap().values()) {
			if (auxStatement instanceof StateRecoverabilityAuxiliaryStatement) {
				StateRecoverabilityAuxiliaryStatement stRecAuxSt = (StateRecoverabilityAuxiliaryStatement) auxStatement;
				if (!vePeaAuxStatementMap.containsKey(stRecAuxSt.getVerificationExpression())) {
					vePeaAuxStatementMap.put(stRecAuxSt.getVerificationExpression(), new HashMap<>());
				}
				Map<PhaseEventAutomata, Set<StateRecoverabilityAuxiliaryStatement>> peaAuxStatementMap =
						vePeaAuxStatementMap.get(stRecAuxSt.getVerificationExpression());
				if (!peaAuxStatementMap.containsKey(stRecAuxSt.getPeaPhasePc().getPea())) {
					peaAuxStatementMap.put(stRecAuxSt.getPeaPhasePc().getPea(), new HashSet<>());
				}
				Set<StateRecoverabilityAuxiliaryStatement> stRecAuxStSet =
						peaAuxStatementMap.get(stRecAuxSt.getPeaPhasePc().getPea());
				stRecAuxStSet.add(stRecAuxSt);
			}
		}
		return vePeaAuxStatementMap;
	}

	public Expression createOppositeCondition(final ILocation loc, BoogieType boogieType, String lhs, String opr,
			String rhs) {
		String newOpr = "";
		switch (opr) {
		case "==":
			newOpr = "!=";
			break;
		case "!=":
			newOpr = "==";
			break;
		case "<":
			newOpr = ">=";
			break;
		case ">":
			newOpr = "<=";
			break;
		case "<=":
			newOpr = ">";
			break;
		case ">=":
			newOpr = "<";
			break;
		default:
			throw new RuntimeException(getClass().getName() + "Could not parse token: " + opr);
		}
		return createExpression(loc, boogieType, lhs, newOpr, rhs);
	}

	public Expression createExpression(final ILocation loc, BoogieType boogieType, String sLhs, Operator opr,
			String sRhs) {
		Expression rhs = null;
		Expression lhs;
		lhs = new IdentifierExpression(loc, boogieType, sLhs, DeclarationInformation.DECLARATIONINFO_GLOBAL);
		switch (boogieType.toString()) {
		case "int":
			rhs = ExpressionFactory.createIntegerLiteral(loc, sRhs);
			break;
		case "bool":
			boolean bValue = "true".equalsIgnoreCase(sRhs) ? true : false;
			rhs = ExpressionFactory.createBooleanLiteral(loc, bValue);
			break;
		case "real":
			rhs = ExpressionFactory.createRealLiteral(loc, sRhs);
			break;
		case "type-error":
			throw new RuntimeErrorException(null, getClass().getName() + ": " + boogieType + " no known data type.");
		}
		Expression expression = ExpressionFactory.newBinaryExpression(loc, opr, lhs, rhs);
		return expression;
	}

	public static Expression createExpression(final ILocation loc, BoogieType boogieType, String sLhs, String sOpr,
			String sRhs) {
		Expression rhs = null;
		Expression lhs;
		BinaryExpression.Operator opr;
		lhs = new IdentifierExpression(loc, boogieType, sLhs, DeclarationInformation.DECLARATIONINFO_GLOBAL);
		switch (boogieType.toString()) {
		case "int":
			rhs = ExpressionFactory.createIntegerLiteral(loc, sRhs);
			break;
		case "bool":
			boolean bValue = "true".equalsIgnoreCase(sRhs) ? true : false;
			rhs = ExpressionFactory.createBooleanLiteral(loc, bValue);
			break;
		case "real":
			rhs = ExpressionFactory.createRealLiteral(loc, sRhs);
			break;
		case "type-error":
			throw new RuntimeErrorException(null,
					StateRecoverabilityGenerator.class.getName() + ": " + boogieType + " no known data type.");
		}
		opr = getOperator(sOpr);
		Expression expression = ExpressionFactory.newBinaryExpression(loc, opr, lhs, rhs);
		return expression;
	}

	private static BinaryExpression.Operator getOperator(String sOpr) {
		switch (sOpr) {
		case "||":
		case "|":
			return Operator.LOGICOR;
		case "&&":
		case "&":
			return Operator.LOGICAND;
		case "==":
			return Operator.COMPEQ;
		case "!=":
			return Operator.COMPNEQ;
		case "<":
			return Operator.COMPLT;
		case ">":
			return Operator.COMPGT;
		case "<=":
			return Operator.COMPLEQ;
		case ">=":
			return Operator.COMPGEQ;
		default:
			throw new RuntimeErrorException(null,
					StateRecoverabilityGenerator.class.getName() + ": Could not parse operator.");
		}
	}
}
