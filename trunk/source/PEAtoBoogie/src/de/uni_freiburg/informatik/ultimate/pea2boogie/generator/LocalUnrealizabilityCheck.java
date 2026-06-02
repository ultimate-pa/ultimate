/*
 * Copyright (C) 2026 Tobias Kolzer (kolzert@informatik.uni-freiburg.de)
 * Copyright (C) 2026 University of Freiburg
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

package de.uni_freiburg.informatik.ultimate.pea2boogie.generator;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.boogie.Boogie2SMT;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.boogie.BoogieDeclarations;
import de.uni_freiburg.informatik.ultimate.lib.pea.CounterTrace;
import de.uni_freiburg.informatik.ultimate.lib.pea.PhaseEventAutomata;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.solverbuilder.SolverBuilder;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.solverbuilder.SolverBuilder.ExternalSolver;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.solverbuilder.SolverBuilder.SolverMode;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.PatternType;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.PatternType.ReqPeas;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.pea2boogie.CddToSmt;
import de.uni_freiburg.informatik.ultimate.pea2boogie.IReqSymbolTable;
import de.uni_freiburg.informatik.ultimate.pea2boogie.PeaResultUtil;
import de.uni_freiburg.informatik.ultimate.util.datastructures.CrossProducts;

public class LocalUnrealizabilityCheck {

	private final Script mScript;
	private final IReqSymbolTable mReqSymbolTable;
	private final Boogie2SMT mBoogie2Smt;
	private final ILogger mLogger;

	private final Map<String, AnnotatedReq> mAnnotatedReqs;

	private record AnnotatedReq(PatternType<?> patternType, PhaseEventAutomata pea,
			Map<Integer, CritPhaseComputer.CritPhase> critPhases) {
	}

	public record Witness(PatternType<?>[] patterns, PhaseEventAutomata[] peas, int[] critPhaseIndices) {
	}

	public LocalUnrealizabilityCheck(final List<ReqPeas> reqPeas, final PeaResultUtil peaResultUtil,
			final BoogieDeclarations boogieDeclarations, final IReqSymbolTable reqSymbolTable,
			final IUltimateServiceProvider services, final ILogger logger) {
		mReqSymbolTable = reqSymbolTable;
		mLogger = logger;

		mScript = SolverBuilder.buildAndInitializeSolver(services, SolverBuilder.constructSolverSettings()
				.setSolverMode(SolverMode.External_ModelsAndUnsatCoreMode).setUseExternalSolver(ExternalSolver.Z3),
				"LocalUnrealizabilitySolver");
		mBoogie2Smt = new Boogie2SMT(new ManagedScript(services, mScript), boogieDeclarations, services, false);
		final CddToSmt cddToSmt =
				new CddToSmt(services, peaResultUtil, mScript, mBoogie2Smt, boogieDeclarations, reqSymbolTable);
		final CritPhaseComputer critPhaseComputer = new CritPhaseComputer(mScript, cddToSmt);

		mAnnotatedReqs = new HashMap<>();
		for (final ReqPeas reqPea : reqPeas) {
			for (final Entry<CounterTrace, PhaseEventAutomata> e : reqPea.getCounterTrace2Pea()) {
				final Map<Integer, CritPhaseComputer.CritPhase> critPhases =
						critPhaseComputer.computeCritPhases(e.getKey(), e.getValue().getName());
				if (!critPhases.isEmpty()) {
					mAnnotatedReqs.put(e.getValue().getName(),
							new AnnotatedReq(reqPea.getPattern(), e.getValue(), critPhases));
				}
			}
		}
	}

	public List<Witness> check(final int subsetSize) {
		final List<AnnotatedReq> reqs = new ArrayList<>(mAnnotatedReqs.values());
		if (reqs.size() < subsetSize) {
			mScript.exit();
			return Collections.emptyList();
		}

		mLogger.info(
				"Checking local unrealizability for " + reqs.size() + " requirements with subset size " + subsetSize);

		final List<Witness> result = new ArrayList<>();
		final AnnotatedReq[] reqArray = reqs.toArray(new AnnotatedReq[0]);
		final List<AnnotatedReq[]> subsets =
				CrossProducts.subArrays(reqArray, subsetSize, new AnnotatedReq[subsetSize]);

		for (final AnnotatedReq[] subset : subsets) {
			final int[][] critPhaseIndexArrays = Arrays.stream(subset)
					.map(ar -> ar.critPhases().keySet().stream().mapToInt(Integer::intValue).toArray())
					.toArray(int[][]::new);

			for (final int[] phaseCombo : CrossProducts.crossProduct(critPhaseIndexArrays)) {
				mLogger.debug("--- Start set for local unrealiyabilitz check");
				final List<Term> vcs = new ArrayList<>();
				for (int i = 0; i < subset.length; i++) {
					mLogger.debug("Req id: " + subset[i].patternType().getId() + " Phase: " + phaseCombo[i]);
					vcs.add(subset[i].critPhases().get(phaseCombo[i]).vc());
				}

				if (isLocallyUnrealizable(vcs)) {
					mLogger.info("Found locally unrealizable subset: "
							+ Arrays.stream(subset).map(ar -> ar.pea().getName()).collect(Collectors.joining(", ")));
					result.add(new Witness(
							Arrays.stream(subset).map(AnnotatedReq::patternType).toArray(PatternType[]::new),
							Arrays.stream(subset).map(AnnotatedReq::pea).toArray(PhaseEventAutomata[]::new),
							phaseCombo));
				}
			}
		}

		mScript.exit();
		return result;
	}

	private boolean isLocallyUnrealizable(final List<Term> vcs) {
		final Term vcDisjunction = SmtUtils.or(mScript, vcs);
		final TermVariable[] freeVarArray = vcDisjunction.getFreeVars();

		final Set<String> inputVarNames = mReqSymbolTable.getInputVars();
		final Set<String> outputVarNames = mReqSymbolTable.getOutputVars();

		final Set<TermVariable> inputVars = new HashSet<>();
		final Set<TermVariable> outputVars = new HashSet<>();

		for (final TermVariable tv : freeVarArray) {
			final var expr = mBoogie2Smt.getTerm2Expression().translate(tv);
			if (!(expr instanceof final IdentifierExpression ie)) {
				continue;
			}
			final String name = ie.getIdentifier();
			if (inputVarNames.contains(name)) {
				inputVars.add(tv);
			} else if (outputVarNames.contains(name)) {
				outputVars.add(tv);
			}
		}

		Term formula = vcDisjunction;
		if (!outputVars.isEmpty()) {
			formula = SmtUtils.quantifier(mScript, QuantifiedFormula.FORALL, outputVars, formula);
		}
		if (!inputVars.isEmpty()) {
			formula = SmtUtils.quantifier(mScript, QuantifiedFormula.EXISTS, inputVars, formula);
		}
		return SmtUtils.checkSatTerm(mScript, formula) == LBool.SAT;
	}
}
