package de.uni_freiburg.informatik.ultimate.pea2boogie.generator;

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
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.boogie.Boogie2SMT;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.boogie.BoogieDeclarations;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.ProgramConst;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.scripttransfer.HistoryRecordingScript;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.scripttransfer.TermTransferrer;
import de.uni_freiburg.informatik.ultimate.lib.pea.CounterTrace;
import de.uni_freiburg.informatik.ultimate.lib.pea.CounterTrace.DCPhase;
import de.uni_freiburg.informatik.ultimate.lib.pea.PhaseEventAutomata;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.NonTheorySymbol;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.NonTheorySymbolFinder;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.solverbuilder.SolverBuilder;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.solverbuilder.SolverBuilder.ExternalSolver;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.solverbuilder.SolverBuilder.SolverMode;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.solverbuilder.SolverBuilder.SolverSettings;
import de.uni_freiburg.informatik.ultimate.lib.srparse.LiteralUtils;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.PatternType;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.PatternType.ReqPeas;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.pea2boogie.CddToSmt;
import de.uni_freiburg.informatik.ultimate.pea2boogie.IReqSymbolTable;
import de.uni_freiburg.informatik.ultimate.pea2boogie.PeaResultUtil;
import de.uni_freiburg.informatik.ultimate.pea2boogie.generator.LiffitonMusExample.MapSolver;
import de.uni_freiburg.informatik.ultimate.pea2boogie.generator.LiffitonMusExample.SubsetSolver;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

public class RtInconsistencyPreCheckMus {
	private final CddToSmtPreCheck mCddToSmtPreCheck;
	private final Script mScript;
	private final ManagedScript mManagedScript;
	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;
	final Map<String, AnnotatedReq> mAnnotatedReqs;

	private record AnnotatedReq(String name, PatternType<?> patternType, CounterTrace counterTrace,
			PhaseEventAutomata pea, Map<Integer, CritPhase> critPhases) {
	}

	private record CritPhase(Integer index, Term invariant, Term nvc, boolean seeping,
			Set<NonTheorySymbol<?>> symbols) {
		public CritPhase(final Integer index, final Term invariant, final Term nvc, final boolean seeping) {
			this(index, invariant, nvc, seeping, new NonTheorySymbolFinder().findNonTheorySymbols(nvc));
		}
	}

	private record MusElement(String reqName, Integer critPhaseIndex, boolean seeping) {
	}

	private record Nvc(String name, Term term, Set<NonTheorySymbol<?>> symbols) {
	}

	public RtInconsistencyPreCheckMus(final List<ReqPeas> reqPeas, final PeaResultUtil peaResultUtil,
			final Boogie2SMT boogie2Smt, final BoogieDeclarations boogieDeclarations,
			final IReqSymbolTable reqSymbolTable, final Script script, final ManagedScript managedScript,
			final IUltimateServiceProvider services, final ILogger logger) {

		mScript = script;
		mManagedScript = managedScript;
		mServices = services;
		mLogger = logger;
		mCddToSmtPreCheck =
				new CddToSmtPreCheck(services, peaResultUtil, script, boogie2Smt, boogieDeclarations, reqSymbolTable);

		mAnnotatedReqs = new HashMap<>();
		for (final var reqPea : reqPeas) {
			for (final Entry<CounterTrace, PhaseEventAutomata> e : reqPea.getCounterTrace2Pea()) {
				mAnnotatedReqs.put(e.getValue().getName(), new AnnotatedReq(e.getValue().getName(), reqPea.getPattern(),
						e.getKey(), e.getValue(), computeCritPhases(e.getKey())));
			}
		}

		// final var s1 = mServices.
		// final var s2 = mScript;
		// final var equal = s1.equals(s2);

		// mLogger.info("");
	}

	public List<Entry<PatternType<?>, PhaseEventAutomata>[]> check() {
		final Set<Set<Nvc>> nvcGroups = groupNvcsBySymbols(new ArrayList<>(mAnnotatedReqs.values()));

		final Set<Set<MusElement>> muses = new HashSet<>();
		for (final var nvcGroup : nvcGroups) {
			mLogger.info("Enumerate Muses of NVC group: " + nvcGroup);
			muses.addAll(enumerateMusesLiffiton(new ArrayList<>(nvcGroup)));
		}
		mLogger.info("Size of nvc muses: " + muses.size());

		muses.removeIf(e -> hasUnsatCritPhases(e, mAnnotatedReqs));
		mLogger.info("Size of nvc muses after filtering unsat crit phases: " + muses.size());

		muses.removeIf(e -> !hasTimeBound(e, mAnnotatedReqs));
		mLogger.info("Size of nvc muses after filtering time bound: " + muses.size());

		mLogger.info("Muses: " + muses);

		final Set<Set<String>> uniqueMuses =
				muses.stream().map(inner -> inner.stream().map(s -> s.reqName()).collect(Collectors.toSet()))
						.collect(Collectors.toSet());

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
					annotatedReqs.get(musElement.reqName()).critPhases().get(musElement.critPhaseIndex()).invariant);
		}

		return LBool.UNSAT == SmtUtils.checkSatTerm(mScript, SmtUtils.and(mScript, critPhaseInvariants));

	}

	private static boolean hasTimeBound(final Set<MusElement> musElements,
			final Map<String, AnnotatedReq> annotatedReqs) {

		return musElements.stream()
				.flatMap(
						musElement -> Arrays.stream(annotatedReqs.get(musElement.reqName()).counterTrace().getPhases()))
				.anyMatch(dcPhase -> dcPhase.getBound() == CounterTrace.BOUND_NONE);
	}

	private Map<Integer, CritPhase> computeCritPhases(final CounterTrace counterTrace) {
		final Map<Integer, CritPhase> results = new HashMap<>();

		final DCPhase[] phases = counterTrace.getPhases();
		final List<Term> seepInvariants = new ArrayList<>(Arrays.asList(mScript.getTheory().mTrue));

		for (int i = phases.length - 2; i >= 0; i--) {
			final DCPhase phase = phases[i];
			final Term invariant = mCddToSmtPreCheck.toSmt(phase.getInvariant());
			final Term seepInvariant = SmtUtils.and(mScript, seepInvariants.getLast(), invariant);

			// Stop if conjunction of subsequent invariants is unsatisfiable.
			if (LBool.UNSAT == SmtUtils.checkSatTerm(mScript, seepInvariants.getLast())) {
				break;
			}

			if (phase.getBoundType() != CounterTrace.BOUND_GREATER
					&& phase.getBoundType() != CounterTrace.BOUND_GREATEREQUAL) {

				// Phase invariant does imply all subsequent invariants, seeping is unavoidable.
				if (mScript.getTheory().mTrue == SmtUtils.implies(mScript, invariant, seepInvariants.getLast())) {
					seepInvariants.add(seepInvariant);
					continue;
				}

				// Found a critical phase without lower bound.
				results.put(i, new CritPhase(i, invariant, SmtUtils.not(mScript, seepInvariants.getLast()),
						results.size() > 0));
				seepInvariants.add(seepInvariant);
			} else {
				// Found a critical phase with lower bound.
				if (mScript.getTheory().mTrue == SmtUtils.implies(mScript, invariant, seepInvariants.getLast())) {
					results.put(i, new CritPhase(i, invariant, SmtUtils.not(mScript, invariant), results.size() > 0));
				} else {
					results.put(i, new CritPhase(i, invariant, SmtUtils.not(mScript, seepInvariants.getLast()),
							results.size() > 0));
				}

				break;
			}
		}
		/*
		 * if (results.isEmpty()) { // Can be skipped. There is no finite prefix such that the requirement is involved
		 * in a rt-inconsistency. results.put(-1, new CritPhase(-1, SmtUtils.not(mScript,
		 * mCddToSmtPreCheck.toSmt(phases[0].getInvariant())), SmtUtils.not(mScript, seepInvariants.getLast()))); }
		 */
		return results;
	}

	private Set<Set<Nvc>> groupNvcsBySymbols(final List<AnnotatedReq> annotatedReqs) {
		// Collect all CritPhases into a list so we can index them for UnionFind
		final List<Pair<String, CritPhase>> critPhases = new ArrayList<>();
		for (final var annotatedReq : annotatedReqs) {
			annotatedReq.critPhases().forEach((phaseIndex, critPhase) -> {
				final String name = annotatedReq.name() + "_" + phaseIndex + (critPhase.seeping ? "s" : "");
				critPhases.add(new Pair<>(name, critPhase));
			});
		}

		final UnionFind unionFind = new UnionFind(critPhases.size());

		// Map each symbol to the list of indices of critPhases that contain it
		final Map<NonTheorySymbol<?>, List<Integer>> symbolToCritPhaseIndices = new HashMap<>();
		for (int i = 0; i < critPhases.size(); i++) {
			final var critPhase = critPhases.get(i).getSecond();
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
		final Map<Integer, Set<Nvc>> groups = new HashMap<>();
		for (int i = 0; i < critPhases.size(); i++) {
			final int root = unionFind.find(i);
			groups.computeIfAbsent(root, k -> new HashSet<>()).add(new Nvc(critPhases.get(i).getFirst(),
					critPhases.get(i).getSecond().nvc(), critPhases.get(i).getSecond().symbols()));
		}

		return new HashSet<>(groups.values());
	}

	private Set<Set<MusElement>> enumerateMusesLiffiton(final ArrayList<Nvc> nvcs) {
		final SolverSettings settings = SolverBuilder.constructSolverSettings()
				.setSolverMode(SolverMode.External_ModelsAndUnsatCoreMode).setUseExternalSolver(ExternalSolver.Z3);
		final Script script = SolverBuilder.buildAndInitializeSolver(mServices, settings, "CSolver");

		final SolverSettings settings2 = SolverBuilder.constructSolverSettings()
				.setSolverMode(SolverMode.External_ModelsAndUnsatCoreMode).setUseExternalSolver(ExternalSolver.Z3);
		final Script script2 = SolverBuilder.buildAndInitializeSolver(mServices, settings2, "MSolver");

		final List<Term> constraints = new ArrayList<>();
		final TermTransferrer termTransferrer = new TermTransferrer(mScript, new HistoryRecordingScript(script));
		for (final Nvc nvc : nvcs) {
			constraints.add(termTransferrer.transform(nvc.term));
		}

		final SubsetSolver csolver = new LiffitonMusExample.SubsetSolver(script, constraints);
		final MapSolver msolver = new LiffitonMusExample.MapSolver(constraints.size(), script2);
		final Iterable<Set<Integer>> muses = LiffitonMusExample.enumerateSets(csolver, msolver, mLogger);
		script.exit();
		script2.exit();

		final Set<Set<MusElement>> result = new HashSet<>();
		for (final var mus : muses) {
			final Set<MusElement> musElements = new HashSet<>();
			for (final var index : mus) {
				final Nvc nvc = nvcs.get(index);
				final String reqName = nvc.name.substring(0, nvc.name.lastIndexOf('_'));
				final String phaseIndexStr = nvc.name.substring(nvc.name.lastIndexOf('_') + 1);
				final boolean seeping = phaseIndexStr.endsWith("s");
				final Integer phaseIndex = Integer
						.parseInt(seeping ? phaseIndexStr.substring(0, phaseIndexStr.length() - 1) : phaseIndexStr);
				musElements.add(new MusElement(reqName, phaseIndex, seeping));
			}
			result.add(musElements);
		}

		return result;
	}

	private void enumerateNvcMusesLiffitonExperiments(final Set<Nvc> nvcs) {
		// mScript.push(1);

		// Plan B: if nothing works, try to call the liffiton script directly
//		try {
//			MonitoredProcess process;
//			final String[] command = { "/usr/bin/python", "-u",
//					"/mnt/Data/Projects/ultimate/releaseScripts/default/adds/hello_world.py" };
//			process = MonitoredProcess.exec(command, null, null, mServices);
//			final BufferedReader reader = new BufferedReader(new InputStreamReader(process.getInputStream()));
//			// reader.close();
//			String line;
//			while ((line = reader.readLine()) != null) {
//				mLogger.info(line);
//			}
//		} catch (final IOException e) {
//			// TODO Auto-generated catch block
//			e.printStackTrace();
//		}

//		final SMTInterpol script = new SMTInterpol();
//		script.setOption(SMTLIBConstants.PRODUCE_UNSAT_CORES, true);
//		script.setOption(SMTLIBConstants.INTERACTIVE_MODE, true);
//		script.setLogic(Logics.ALL);

		final SolverSettings settings1 = SolverBuilder.constructSolverSettings()
				.setSolverMode(SolverMode.External_ModelsAndUnsatCoreMode).setUseExternalSolver(ExternalSolver.Z3);
		final Script script1 = SolverBuilder.buildAndInitializeSolver(mServices, settings1, "CSolver");

//		final SolverSettings settings2 = SolverBuilder.constructSolverSettings()
//				.setSolverMode(SolverMode.External_ModelsAndUnsatCoreMode).setUseExternalSolver(ExternalSolver.Z3);
//		final Script script2 = SolverBuilder.buildAndInitializeSolver(mServices, settings2, "MSolver");

		final List<Term> constraints = new ArrayList<>();
		final TermTransferrer termTransferrer = new TermTransferrer(mScript, new HistoryRecordingScript(script1));
		for (final Nvc nvc : nvcs) {
			constraints.add(termTransferrer.transform(nvc.term));
		}

		// final List constraints = nvcs.stream().map(nvc -> nvc.term).collect(Collectors.toList());

		final SubsetSolver csolver = new LiffitonMusExample.SubsetSolver(script1, constraints);
		final MapSolver msolver = new LiffitonMusExample.MapSolver(constraints.size());
		final var muses = LiffitonMusExample.enumerateSets(csolver, msolver, mLogger);

		script1.exit();
		// script2.exit();

		// mScript.pop(1);
	}

//	private Set<Set<MusElement>> enumerateNvcMuses(final Set<Nvc> nvcs) {
//		Set<Set<MusElement>> result = new HashSet<>();
//
//		final SMTInterpol smtInterpol = new SMTInterpol();
//		smtInterpol.setOption(SMTLIBConstants.PRODUCE_UNSAT_CORES, true);
//		smtInterpol.setOption(SMTLIBConstants.INTERACTIVE_MODE, true);
//		// smtInterpol.setLogic(Logics.ALL);
//		smtInterpol.setLogic(Logics.QF_UFLIRA);
//
//		final MusEnumerationScript musEnumerationScript = new MusEnumerationScript(smtInterpol);
//		musEnumerationScript.setOption(MusOptions.LOG_ADDITIONAL_INFORMATION, false);
//		// musEnumerationScript.setOption(MusOptions.UNKNOWN_ALLOWED, true);
//		// musEnumerationScript.setOption(SMTLIBConstants.RANDOM_SEED, 1337);
//
//		final TermTransferrer termTransferrer =
//				new TermTransferrer(mScript, new HistoryRecordingScript(musEnumerationScript));
//
//		for (final var nvc : nvcs) {
//			musEnumerationScript.assertTerm(musEnumerationScript.annotate(termTransferrer.transform(nvc.term),
//					new Annotation(":named", nvc.name)));
//
//			final String symbols_string = nvc.symbols.stream().map(
//					s -> String.format("(%s, %s)", s, ((ApplicationTerm) s.getSymbol()).getFunction().getReturnSort()))
//					.collect(Collectors.joining(", "));
//
//			mLogger.info(String.format("Assert NVC for MUS enumeration: name=\"%s\", nvc=\"%s\", symbols=\"%s\"",
//					nvc.name, nvc.term, symbols_string));
//		}
//
//		final LBool sat = musEnumerationScript.checkSat();
//		mLogger.info("Check sat of nvcs in group: " + sat);
//
//		if (LBool.UNSAT == musEnumerationScript.checkSat()) {
//			result = getUnsatCores(musEnumerationScript).stream().map(core -> core.stream().map(s -> {
//				final String reqName = s.substring(0, s.lastIndexOf('_'));
//				final String index = s.substring(s.lastIndexOf('_') + 1);
//				final boolean seeping = index.endsWith("s");
//				return new MusElement(reqName,
//						Integer.parseInt(seeping ? index.substring(0, index.length() - 1) : index), seeping);
//			}).collect(Collectors.toSet())).collect(Collectors.toSet());
//		}
//
//		return result;
//	}

//	private ArrayList<ArrayList<String>> getUnsatCores(final MusEnumerationScript musEnumerationScript) {
//		if (!musEnumerationScript.mAssertedTermsAreUnsat) {
//			throw new SMTLIBException("Call checkSat to determine satisfiability.");
//		}
//
//		if (!((boolean) musEnumerationScript.getOption(SMTLIBConstants.PRODUCE_UNSAT_CORES))) {
//			throw new SMTLIBException("Unsat core production must be enabled (you can do this via setOption).");
//		}
//
//		final Translator translator = new Translator();
//		final ArrayList<MusContainer> muses = musEnumerationScript.executeReMus(translator);
//
//		final ArrayList<ArrayList<String>> unsatCores = new ArrayList<>();
//		for (final var mus : muses) {
//			final ArrayList<String> unsatCore = new ArrayList<>();
//
//			for (final Term term : translator.translateToTerms(mus.getMus())) {
//				if (!(term instanceof final AnnotatedTerm annotatedTerm)) {
//					continue;
//				}
//
//				for (final Annotation annotation : annotatedTerm.getAnnotations()) {
//					if (":named".equals(annotation.getKey())) {
//						unsatCore.add(((String) annotation.getValue()).intern());
//						break;
//					}
//				}
//			}
//			unsatCores.add(unsatCore);
//		}
//
//		return unsatCores;
//	}

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

	private static class UnionFind {

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
