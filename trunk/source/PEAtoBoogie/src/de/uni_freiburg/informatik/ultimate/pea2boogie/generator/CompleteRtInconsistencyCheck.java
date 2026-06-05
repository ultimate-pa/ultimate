/*
 * Copyright (C) 2026 Nico Hauff (hauffn@informatik.uni-freiburg.de)
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

import java.io.BufferedReader;
import java.io.InputStreamReader;
import java.util.AbstractMap;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Optional;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.output.BoogiePrettyPrinter;
import de.uni_freiburg.informatik.ultimate.core.lib.util.MonitoredProcess;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.boogie.Boogie2SMT;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.boogie.BoogieDeclarations;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.ProgramConst;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.scripttransfer.HistoryRecordingScript;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.scripttransfer.TermTransferrer;
import de.uni_freiburg.informatik.ultimate.lib.pea.CounterTrace;
import de.uni_freiburg.informatik.ultimate.lib.pea.PhaseEventAutomata;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.NonTheorySymbol;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.solverbuilder.SolverBuilder;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.solverbuilder.SolverBuilder.ExternalSolver;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.solverbuilder.SolverBuilder.SolverMode;
import de.uni_freiburg.informatik.ultimate.lib.srparse.LiteralUtils;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.PatternType;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.PatternType.ReqPeas;
import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.pea2boogie.CddToSmt;
import de.uni_freiburg.informatik.ultimate.pea2boogie.IReqSymbolTable;
import de.uni_freiburg.informatik.ultimate.pea2boogie.PeaResultUtil;
import de.uni_freiburg.informatik.ultimate.pea2boogie.generator.MusEnumerator.MapSolver;
import de.uni_freiburg.informatik.ultimate.pea2boogie.generator.MusEnumerator.MusEnumeratorResult;
import de.uni_freiburg.informatik.ultimate.pea2boogie.generator.MusEnumerator.SubsetSolver;
import de.uni_freiburg.informatik.ultimate.pea2boogie.preferences.Pea2BoogiePreferences.CompleteRtInconsistencyCheckMode;
import de.uni_freiburg.informatik.ultimate.smtinterpol.muses.MusContainer;
import de.uni_freiburg.informatik.ultimate.smtinterpol.muses.MusEnumerationScript;
import de.uni_freiburg.informatik.ultimate.smtinterpol.muses.MusOptions;
import de.uni_freiburg.informatik.ultimate.smtinterpol.muses.Translator;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.SMTInterpol;

public class CompleteRtInconsistencyCheck {
	private final CddToSmtPreCheck mCddToSmtPreCheck;
	private final Script mScript;
	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;
	private final CompleteRtInconsistencyCheckMode mMode;
	final Map<String, AnnotatedReq> mAnnotatedReqs;

	private record AnnotatedReq(String name, PatternType<?> patternType, CounterTrace counterTrace,
			PhaseEventAutomata pea, Map<Integer, CritPhaseComputer.CritPhase> critPhases) {
	}

	private record MusElement(String reqName, Integer critPhaseIndex, boolean seeping) {
	}

	public CompleteRtInconsistencyCheck(final List<ReqPeas> reqPeas, final PeaResultUtil peaResultUtil,
			final Boogie2SMT boogie2Smt, final BoogieDeclarations boogieDeclarations,
			final IReqSymbolTable reqSymbolTable, final Script script, final IUltimateServiceProvider services,
			final ILogger logger, final CompleteRtInconsistencyCheckMode mode) {

		mScript = script;
		mServices = services;
		mLogger = logger;
		mMode = mode;
		mCddToSmtPreCheck =
				new CddToSmtPreCheck(services, peaResultUtil, script, boogie2Smt, boogieDeclarations, reqSymbolTable);
		final CritPhaseComputer critPhaseComputer = new CritPhaseComputer(script, mCddToSmtPreCheck);

		mAnnotatedReqs = new HashMap<>();
		for (final var reqPea : reqPeas) {
			for (final Entry<CounterTrace, PhaseEventAutomata> e : reqPea.getCounterTrace2Pea()) {
				mAnnotatedReqs.put(e.getValue().getName(),
						new AnnotatedReq(e.getValue().getName(), reqPea.getPattern(), e.getKey(), e.getValue(),
								critPhaseComputer.computeCritPhases(e.getKey(), e.getValue().getName())));
			}
		}
	}

	public List<Entry<PatternType<?>, PhaseEventAutomata>[]> check() {
		// TODO: Add option to filter groups and muses with size 1

		final Set<Set<CritPhaseComputer.CritPhase>> groups =
				groupNvcsBySymbols(new ArrayList<>(mAnnotatedReqs.values()));

		final Set<Set<MusElement>> muses = new HashSet<>();
		for (final var group : groups) {
			if (group.size() <= 1) {
				continue;
			}

			mLogger.info("Enumerate muses of nvc group size: " + group.size());
			if (mMode == CompleteRtInconsistencyCheckMode.MARCO_BASIC) {
				muses.addAll(enumerateMusesMarcoBasic(new ArrayList<>(group)));
			} else if (mMode == CompleteRtInconsistencyCheckMode.REMUS) {
				muses.addAll(enumerateMusesRemus(group));
			} else if (mMode == CompleteRtInconsistencyCheckMode.EXPERIMENTAL_PYTHON) {
				muses.addAll(enumerateMusesPython(new ArrayList<>(group)));
			} else {
				throw new IllegalArgumentException("Unknown CompleteRtInconsistencyCheckMode: " + mMode);
			}
		}
		mLogger.info("Size of nvc muses: " + muses.size());

		muses.removeIf(e -> hasUnsatCritPhases(e, mAnnotatedReqs));
		mLogger.info("Size of nvc muses after filtering unsat crit phases: " + muses.size());

		// TODO: Check if it is correct to filter muses without lower time bound
		muses.removeIf(e -> !hasTimeBound(e, mAnnotatedReqs));
		mLogger.info("Size of nvc muses after filtering time bound: " + muses.size());

		final Set<Set<String>> uniqueMuses =
				muses.stream().map(inner -> inner.stream().map(s -> s.reqName()).collect(Collectors.toSet()))
						.collect(Collectors.toSet());

		mLogger.info("Size of unique muses wrt. reqIds: " + uniqueMuses.size());
		mLogger.info("Size distribution of unique muses: "
				+ uniqueMuses.stream().collect(Collectors.groupingBy(Set::size, Collectors.counting())).entrySet()
						.stream().sorted(Map.Entry.comparingByKey())
						.map(e -> "(" + e.getKey() + ": " + e.getValue() + ")").collect(Collectors.joining(", ")));

		final List<Entry<PatternType<?>, PhaseEventAutomata>[]> result =
				uniqueMuses.stream().map(mus -> mus.stream().map(name -> {
					final AnnotatedReq annotatedReq = mAnnotatedReqs.get(name);
					return new AbstractMap.SimpleEntry<>(annotatedReq.patternType(), annotatedReq.pea());
				}).toArray(Entry[]::new)).collect(Collectors.toList());

		return result;
	}

	private boolean hasUnsatCritPhases(final Set<MusElement> musElements,
			final Map<String, AnnotatedReq> annotatedReqs) {
		final ArrayList<Term> critPhaseInvariants = new ArrayList<>();

		for (final var musElement : musElements) {
			critPhaseInvariants.add(
					annotatedReqs.get(musElement.reqName()).critPhases().get(musElement.critPhaseIndex()).invariant());
		}

		return LBool.UNSAT == SmtUtils.checkSatTerm(mScript, SmtUtils.and(mScript, critPhaseInvariants));
	}

	private static boolean hasTimeBound(final Set<MusElement> musElements,
			final Map<String, AnnotatedReq> annotatedReqs) {

		return musElements.stream()
				.flatMap(
						musElement -> Arrays.stream(annotatedReqs.get(musElement.reqName()).counterTrace().getPhases()))
				.anyMatch(dcPhase -> (dcPhase.getBoundType() == CounterTrace.BOUND_GREATER
						|| dcPhase.getBoundType() == CounterTrace.BOUND_GREATEREQUAL));

//		return musElements.stream()
//				.flatMap(
//						musElement -> Arrays.stream(annotatedReqs.get(musElement.reqName()).counterTrace().getPhases()))
//				.anyMatch(dcPhase -> dcPhase.getBoundType() != CounterTrace.BOUND_NONE);
	}

	private Set<Set<CritPhaseComputer.CritPhase>> groupNvcsBySymbols(final List<AnnotatedReq> annotatedReqs) {
		final List<CritPhaseComputer.CritPhase> critPhases =
				annotatedReqs.stream().flatMap(ar -> ar.critPhases().values().stream()).collect(Collectors.toList());

		final UnionFind unionFind = new UnionFind(critPhases.size());

		// Map each symbol to the list of indices of critPhases that contain it
		final Map<NonTheorySymbol<?>, List<Integer>> symbolToCritPhaseIndices = new HashMap<>();
		for (int i = 0; i < critPhases.size(); i++) {
			final var critPhase = critPhases.get(i);
			for (final var symbol : critPhase.symbols()) {
				symbolToCritPhaseIndices.computeIfAbsent(symbol, k -> new ArrayList<>()).add(i);
			}
		}

		// Union critPhases that share a symbol
		for (final var indices : symbolToCritPhaseIndices.values()) {
			assert !indices.isEmpty();

			final int first = indices.get(0);
			for (int j = 1; j < indices.size(); j++) {
				unionFind.union(first, indices.get(j));
			}
		}

		// Group by root
		final Map<Integer, Set<CritPhaseComputer.CritPhase>> groups = new HashMap<>();
		for (int i = 0; i < critPhases.size(); i++) {
			final int root = unionFind.find(i);
			groups.computeIfAbsent(root, k -> new HashSet<>()).add(critPhases.get(i));
		}

		return new HashSet<>(groups.values());
	}

	private Set<Set<MusElement>> enumerateMusesMarcoBasic(final List<CritPhaseComputer.CritPhase> critPhases) {
		final Script scriptCSolver = SolverBuilder.buildAndInitializeSolver(mServices,
				SolverBuilder.constructSolverSettings().setSolverMode(SolverMode.External_ModelsAndUnsatCoreMode)
						.setUseExternalSolver(ExternalSolver.Z3),
				"CSolver");

		final Script scriptMSolver = SolverBuilder.buildAndInitializeSolver(mServices,
				SolverBuilder.constructSolverSettings().setSolverMode(SolverMode.External_ModelsMode)
						.setUseExternalSolver(ExternalSolver.Z3),
				"MSolver");

		final TermTransferrer termTransferrer = new TermTransferrer(mScript, new HistoryRecordingScript(scriptCSolver));
		final List<Term> constraints = critPhases.stream().map(critPhase -> termTransferrer.transform(critPhase.nvc()))
				.collect(Collectors.toList());

		final SubsetSolver cSolver = new MusEnumerator.SubsetSolver(scriptCSolver, constraints);
		final MapSolver mSolver = new MusEnumerator.MapSolver(scriptMSolver, constraints.size());
		final List<MusEnumeratorResult> musResults = MusEnumerator.enumerate(cSolver, mSolver, mLogger);
		scriptCSolver.exit();
		scriptMSolver.exit();

		final Set<Set<MusElement>> result =
				musResults
						.stream().filter(musResult -> musResult.type() == MusEnumeratorResult.Type.MUS).map(
								musResult -> musResult.indices().stream().map(critPhases::get)
										.map(critPhase -> new MusElement(critPhase.reqName(), critPhase.index(),
												critPhase.seeping()))
										.collect(Collectors.toSet()))
						.collect(Collectors.toSet());

		return result;
	}

	private Set<Set<MusElement>> enumerateMusesPython(final List<CritPhaseComputer.CritPhase> critPhases) {
		final Set<Set<MusElement>> result = new HashSet<>();

		final String json = critPhases.stream().map(critPhase -> {
			final String symbols = critPhase.symbols().stream()
					.map(symbol -> String.format("{\"name\": \"%s\", \"sort\": \"%s\"}", symbol,
							((ApplicationTerm) symbol.getSymbol()).getFunction().getReturnSort()))
					.collect(Collectors.joining(", "));
			final String name = critPhase.reqName() + "_" + critPhase.index() + (critPhase.seeping() ? "s" : "");

			return String.format("{\"name\": \"%s\", \"smt_expr\": \"%s\", \"symbols\": [%s]}", name, critPhase.nvc(),
					symbols);
		}).collect(Collectors.joining("\n"));

		final String[] command = { "mus_enumerator", json + "\n" };
		try (final MonitoredProcess process = MonitoredProcess.exec(command, null, null, mServices)) {
			final BufferedReader input = new BufferedReader(new InputStreamReader(process.getInputStream()));
			final BufferedReader error = new BufferedReader(new InputStreamReader(process.getErrorStream()));

			input.lines().filter(line -> line.startsWith("MUS")).forEach(line -> {
				mLogger.info(line);

				final String[] parts = line.split("\\|");
				final Set<MusElement> musElement = Arrays.stream(parts[1].trim().substring(4).split(","))
						.map(String::trim).map(Integer::parseInt).map(critPhases::get)
						.map(critPhase -> new MusElement(critPhase.reqName(), critPhase.index(), critPhase.seeping()))
						.collect(Collectors.toSet());
				result.add(musElement);
			});

			error.lines().forEach(line -> mLogger.error("mus_enumerator stderr: " + line));

		} catch (final Exception e) {
			mLogger.fatal("Failed to start mus_enumerator process: ", e);
		}

		return result;
	}

	private Set<Set<MusElement>> enumerateMusesRemus(final Set<CritPhaseComputer.CritPhase> critPhases) {
		Set<Set<MusElement>> result = new HashSet<>();

		final SMTInterpol smtInterpol = new SMTInterpol();
		smtInterpol.setOption(SMTLIBConstants.PRODUCE_UNSAT_CORES, true);
		smtInterpol.setOption(SMTLIBConstants.INTERACTIVE_MODE, true);
		smtInterpol.setLogic(Logics.ALL);

		final MusEnumerationScript musEnumerationScript = new MusEnumerationScript(smtInterpol);
		musEnumerationScript.setOption(MusOptions.LOG_ADDITIONAL_INFORMATION, false);
		// musEnumerationScript.setOption(MusOptions.UNKNOWN_ALLOWED, true);

		final TermTransferrer termTransferrer =
				new TermTransferrer(mScript, new HistoryRecordingScript(musEnumerationScript));

		for (final CritPhaseComputer.CritPhase critPhase : critPhases) {
			final String name = critPhase.reqName() + "_" + critPhase.index() + (critPhase.seeping() ? "s" : "");
			musEnumerationScript.assertTerm(musEnumerationScript.annotate(termTransferrer.transform(critPhase.nvc()),
					new Annotation(":named", name)));

			final String symbols = critPhase.symbols().stream()
					.map(symbol -> String.format("(%s, %s)", symbol,
							((ApplicationTerm) symbol.getSymbol()).getFunction().getReturnSort()))
					.collect(Collectors.joining(", "));

			mLogger.info(String.format("Assert nvc for mus enumeration: name=\"%s\", smt_expr=\"%s\", symbols=\"%s\"",
					name, critPhase.nvc(), symbols));
		}

		final LBool sat = musEnumerationScript.checkSat();
		mLogger.info("Check sat of asserted nvcs in group: " + sat);

		if (LBool.UNSAT == musEnumerationScript.checkSat()) {
			result = getUnsatCores(musEnumerationScript).stream().map(core -> core.stream().map(s -> {
				final String reqName = s.substring(0, s.lastIndexOf('_'));
				final String index = s.substring(s.lastIndexOf('_') + 1);
				final boolean seeping = index.endsWith("s");
				return new MusElement(reqName,
						Integer.parseInt(seeping ? index.substring(0, index.length() - 1) : index), seeping);
			}).collect(Collectors.toSet())).collect(Collectors.toSet());
		}

		return result;
	}

	private ArrayList<ArrayList<String>> getUnsatCores(final MusEnumerationScript musEnumerationScript) {
		if (!musEnumerationScript.mAssertedTermsAreUnsat) {
			throw new SMTLIBException("Call checkSat to determine satisfiability.");
		}

		if (!((boolean) musEnumerationScript.getOption(SMTLIBConstants.PRODUCE_UNSAT_CORES))) {
			throw new SMTLIBException("Unsat core production must be enabled (you can do this via setOption).");
		}

		final Translator translator = new Translator();
		final ArrayList<MusContainer> muses = musEnumerationScript.executeReMus(translator);

		final ArrayList<ArrayList<String>> unsatCores = new ArrayList<>();
		for (final var mus : muses) {
			final ArrayList<String> unsatCore = new ArrayList<>();

			for (final Term term : translator.translateToTerms(mus.getMus())) {
				if (!(term instanceof final AnnotatedTerm annotatedTerm)) {
					continue;
				}

				for (final Annotation annotation : annotatedTerm.getAnnotations()) {
					if (":named".equals(annotation.getKey())) {
						unsatCore.add(((String) annotation.getValue()).intern());
						break;
					}
				}
			}
			unsatCores.add(unsatCore);
		}

		return unsatCores;
	}

	private class CddToSmtPreCheck extends CddToSmt {
		private final Map<Term, Term> mConstants;

		public CddToSmtPreCheck(final IUltimateServiceProvider services, final PeaResultUtil resultUtil,
				final Script script, final Boogie2SMT boogieToSmt, final BoogieDeclarations boogieDeclarations,
				final IReqSymbolTable symboltable) {
			super(services, resultUtil, script, boogieToSmt, boogieDeclarations, symboltable);

			mConstants = createConstToValue(script, symboltable, boogieToSmt);
		}

		@Override
		public Term getTermVarTerm(final String name) {
			final IProgramNonOldVar programVar = mBoogieToSmt.getBoogie2SmtSymbolTable().getGlobalsMap().get(name);
			if (programVar != null) {
				return termVariableToConstant(mScript, (TermVariable) programVar.getTerm());
			}

			final ProgramConst programConst = mBoogieToSmt.getBoogie2SmtSymbolTable().getConstsMap().get(name);
			if (programConst != null) {
				return mConstants.get(programConst.getDefaultConstant());
			}
			throw new AssertionError("Unknown symbol " + name);
		}

		private static Term termVariableToConstant(final Script script, final TermVariable tv) {
			final String name = tv.getName() + "_const_" + tv.hashCode();
			final Sort[] paramSorts = {};
			final Sort resultSort = tv.getSort();

			if (script.getTheory().getFunctionSymbol(name) == null) {
				script.declareFun(name, paramSorts, resultSort);
			}

			return script.term(name);
		}

		private static Map<Term, Term> createConstToValue(final Script script, final IReqSymbolTable reqSymboltable,
				final Boogie2SMT boogieToSmt) {
			final Map<String, Expression> constToValue = reqSymboltable.getConstToValue();
			final Map<String, ProgramConst> boogieConsts = boogieToSmt.getBoogie2SmtSymbolTable().getConstsMap();

			final Map<Term, Term> rtr = new HashMap<>();
			for (final Entry<String, Expression> constEntry : constToValue.entrySet()) {
				final ProgramConst programConst = boogieConsts.get(constEntry.getKey());
				final Optional<Term> value = LiteralUtils.toTerm(constEntry.getValue(), script);
				if (!value.isPresent()) {
					throw new IllegalArgumentException(
							BoogiePrettyPrinter.print(constEntry.getValue()) + " is no literal");
				}
				rtr.put(programConst.getTerm(), value.get());
			}

			return rtr;
		}
	}

	static class UnionFind {

		private final int[] parent;
		private final int[] rank;

		/**
		 * Create a UnionFind for elements 0..n-1.
		 *
		 * @param n
		 *            number of elements (must be >= 0)
		 */
		public UnionFind(final int n) {
			if (n < 0) {
				throw new IllegalArgumentException("n must be non-negative");
			}
			parent = new int[n];
			rank = new int[n];
			for (int i = 0; i < n; i++) {
				parent[i] = i;
				rank[i] = 0;
			}
		}

		/**
		 * Find the representative (root) of the set that contains x. Uses path compression to flatten the tree.
		 *
		 * @param x
		 *            element index
		 * @return root of the set containing x
		 * @throws IndexOutOfBoundsException
		 *             if x is outside [0, n)
		 */
		public int find(final int x) {
			checkIndex(x);
			if (parent[x] != x) {
				parent[x] = find(parent[x]);
			}
			return parent[x];
		}

		/**
		 * Union the sets containing x and y. If already in the same set, does nothing. Uses union by rank.
		 *
		 * @param x
		 *            element index
		 * @param y
		 *            element index
		 * @throws IndexOutOfBoundsException
		 *             if x or y is outside [0, n)
		 */
		public void union(final int x, final int y) {
			final int rootX = find(x);
			final int rootY = find(y);

			if (rootX == rootY) {
				return; // already in same set
			}

			if (rank[rootX] < rank[rootY]) {
				parent[rootX] = rootY;
			} else if (rank[rootX] > rank[rootY]) {
				parent[rootY] = rootX;
			} else {
				parent[rootY] = rootX;
				rank[rootX]++;
			}
		}

		/**
		 * Return true if x and y are in the same set.
		 */
		public boolean connected(final int x, final int y) {
			return find(x) == find(y);
		}

		/**
		 * Number of elements managed by this UnionFind.
		 */
		public int size() {
			return parent.length;
		}

		private void checkIndex(final int x) {
			if (x < 0 || x >= parent.length) {
				throw new IndexOutOfBoundsException("Index out of range: " + x);
			}
		}
	}
}
