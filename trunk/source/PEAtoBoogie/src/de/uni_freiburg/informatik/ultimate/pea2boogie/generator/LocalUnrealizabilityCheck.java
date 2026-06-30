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
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.NoSuchElementException;
import java.util.Objects;
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
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.NonTheorySymbol;
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

	public List<Witness> check(final int maxSubsetSize) {
		final List<AnnotatedReq> reqs = new ArrayList<>(mAnnotatedReqs.values());
		if (reqs.isEmpty()) {
			mScript.exit();
			return Collections.emptyList();
		}

		final Set<Set<AnnotatedReq>> groups = groupVcsBySymbols(reqs);
		mLogger.info("INPUTS: " + mReqSymbolTable.getInputVars());
		final Set<String> tmp = new HashSet<>(mReqSymbolTable.getStateVars());
		tmp.removeAll(mReqSymbolTable.getInputVars());
		mLogger.info("OUTPUTS: " + tmp);
		mLogger.info("Checking local unrealizability: " + reqs.size() + " requirements in " + groups.size()
				+ " variable groups, max subset size " + maxSubsetSize);

		final List<Witness> result = new ArrayList<>();
		for (final Set<AnnotatedReq> group : groups) {
			result.addAll(findMinimalInGroup(new ArrayList<>(group), maxSubsetSize));
		}

		mScript.exit();
		mLogger.info("Found " + result.size() + " locally unrealizable subsets");
		return result;
	}

	private Set<Set<AnnotatedReq>> groupVcsBySymbols(final List<AnnotatedReq> reqs) {
		final CompleteRtInconsistencyCheck.UnionFind unionFind =
				new CompleteRtInconsistencyCheck.UnionFind(reqs.size()); // could be in its own class an not in
																			// CompleteRtInconsistencyCheck

		// final Set<String> outputVarNames = mReqSymbolTable.getOutputVars();
		final Set<String> outputVarNames = new HashSet<>(mReqSymbolTable.getStateVars());
		outputVarNames.removeAll(mReqSymbolTable.getInputVars());
		final Map<NonTheorySymbol<?>, List<Integer>> symbolToReqIndices = new HashMap<>();
		for (int i = 0; i < reqs.size(); i++) {
			for (final CritPhaseComputer.CritPhase critPhase : reqs.get(i).critPhases().values()) {
				for (final NonTheorySymbol<?> symbol : critPhase.symbols()) {
					if (!isOutputSymbol(symbol, outputVarNames)) {
						continue;
					}
					symbolToReqIndices.computeIfAbsent(symbol, k -> new ArrayList<>()).add(i);
				}
			}
		}

		// Union requirements that share a symbol
		for (final List<Integer> indices : symbolToReqIndices.values()) {
			final int first = indices.get(0);
			for (int j = 1; j < indices.size(); j++) {
				unionFind.union(first, indices.get(j));
			}
		}

		// Collect groups by root
		final Map<Integer, Set<AnnotatedReq>> groups = new HashMap<>();
		for (int i = 0; i < reqs.size(); i++) {
			groups.computeIfAbsent(unionFind.find(i), k -> new HashSet<>()).add(reqs.get(i));
		}
		return new HashSet<>(groups.values());
	}

	@SuppressWarnings("unchecked")
	private List<Witness> findMinimalInGroup(final List<AnnotatedReq> group, final int maxSubsetSize) {
		// check if whole set is locally unrealizable, if not no subset can be
		final List<Term> allVcs = new ArrayList<>();
		for (final AnnotatedReq ar : group) {
			for (final CritPhaseComputer.CritPhase phase : ar.critPhases().values()) {
				allVcs.add(phase.vc());
			}
		}
		if (!isLocallyUnrealizable(allVcs)) {
			return Collections.emptyList();
		}

		final List<Witness> result = new ArrayList<>();
		final List<Set<Entry<String, Integer>>> foundMinimalCombinations = new ArrayList<>();

		final int limit = Math.min(maxSubsetSize, group.size());
		mLogger.info("max size: " + limit);
		for (int size = 1; size <= limit; size++) {
			final AnnotatedReq[] groupArray = group.toArray(new AnnotatedReq[0]);
			mLogger.info("curren size: " + size);
			for (final AnnotatedReq[] subset : subArraysLazy(groupArray, size, new AnnotatedReq[size])) {

				final int[][] critPhaseIndexArrays = Arrays.stream(subset)
						.map(ar -> ar.critPhases().keySet().stream().mapToInt(Integer::intValue).toArray())
						.toArray(int[][]::new);

				for (final int[] phaseCombo : CrossProducts.crossProduct(critPhaseIndexArrays)) {
					final Map<String, Integer> candidateMap = new HashMap<>();
					for (int i = 0; i < subset.length; i++) {
						candidateMap.put(subset[i].pea().getName(), phaseCombo[i]);
					}

					if (isSupersetOfFound(candidateMap, foundMinimalCombinations)) {
						continue;
					}

					if (!areSymbolsConnected(subset, phaseCombo)) {
						continue;
					}

					mLogger.debug("Checking local unrealizability for: " + Arrays.stream(subset)
							.map(ar -> ar.patternType().getId()).collect(Collectors.joining(", ")) + " phases: "
							+ Arrays.toString(phaseCombo));

					final List<Term> vcs = new ArrayList<>();
					for (int i = 0; i < subset.length; i++) {
						vcs.add(subset[i].critPhases().get(phaseCombo[i]).vc());
					}

					if (isLocallyUnrealizable(vcs)) {
						mLogger.info("Found locally unrealizable subset: "
								+ Arrays.stream(subset).map(ar -> ar.pea().getName()).collect(Collectors.joining(", "))
								+ " phases: " + Arrays.toString(phaseCombo));
						foundMinimalCombinations.add(new HashSet<>(candidateMap.entrySet()));
						result.add(new Witness(
								Arrays.stream(subset).map(AnnotatedReq::patternType).toArray(PatternType[]::new),
								Arrays.stream(subset).map(AnnotatedReq::pea).toArray(PhaseEventAutomata[]::new),
								phaseCombo));
					}
				}
			}
		}
		return result;
	}

	private boolean isOutputSymbol(final NonTheorySymbol<?> symbol, final Set<String> outputVarNames) {
		if (!(symbol instanceof NonTheorySymbol.Variable)) {
			return false;
		}
		final TermVariable tv = ((NonTheorySymbol.Variable) symbol).getSymbol();
		final var expr = mBoogie2Smt.getTerm2Expression().translate(tv);
		if (!(expr instanceof final IdentifierExpression ie)) {
			return false;
		}
		return outputVarNames.contains(ie.getIdentifier());
	}

	private static boolean isSupersetOfFound(final Map<String, Integer> candidateMap,
			final List<Set<Entry<String, Integer>>> foundMinimal) {
		return foundMinimal.stream().anyMatch(
				found -> found.stream().allMatch(e -> Objects.equals(candidateMap.get(e.getKey()), e.getValue())));
	}

	@SuppressWarnings("unchecked")
	private static boolean areSymbolsConnected(final AnnotatedReq[] subset, final int[] phaseCombo) {
		if (subset.length <= 1) {
			return true;
		}
		final Set<NonTheorySymbol<?>>[] symbolSets = new Set[subset.length];
		for (int i = 0; i < subset.length; i++) {
			symbolSets[i] = subset[i].critPhases().get(phaseCombo[i]).symbols();
		}
		final boolean[] visited = new boolean[subset.length];
		visited[0] = true;
		boolean changed = true;
		while (changed) {
			changed = false;
			for (int i = 0; i < subset.length; i++) {
				if (!visited[i]) {
					continue;
				}
				for (int j = 0; j < subset.length; j++) {
					if (!visited[j] && !Collections.disjoint(symbolSets[i], symbolSets[j])) {
						visited[j] = true;
						changed = true;
					}
				}
			}
		}
		for (final boolean v : visited) {
			if (!v) {
				return false;
			}
		}
		return true;
	}

	/**
	 * Generates all k-element subarrays of input lazily using the next-k-combination algorithm (Knuth TAOCP Vol. 4A,
	 * Algorithm L). Uses O(k) memory instead of materializing all C(n,k) combinations at once.
	 *
	 * <b>IMPORTANT:</b> The returned array instance is reused across iterations. Do not store it beyond the loop body.
	 */
	private static <T> Iterable<T[]> subArraysLazy(final T[] input, final int k, final T[] intermediateArray) {
		return () -> new Iterator<>() {
			private final int n = input.length;
			private final int[] indices = initIndices();
			private boolean hasNext = k <= n;

			private int[] initIndices() {
				final int[] idx = new int[k];
				for (int i = 0; i < k; i++) {
					idx[i] = i;
				}
				return idx;
			}

			@Override
			public boolean hasNext() {
				return hasNext;
			}

			@Override
			public T[] next() {
				if (!hasNext) {
					throw new NoSuchElementException();
				}
				for (int i = 0; i < k; i++) {
					intermediateArray[i] = input[indices[i]];
				}
				int p = k - 1;
				while (p >= 0 && indices[p] == n - k + p) {
					p--;
				}
				if (p < 0) {
					hasNext = false;
				} else {
					indices[p]++;
					for (int j = p + 1; j < k; j++) {
						indices[j] = indices[p] + (j - p);
					}
				}
				return intermediateArray;
			}
		};
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
