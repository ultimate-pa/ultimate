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

import java.util.AbstractMap;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Comparator;
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
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.NonTheorySymbol;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.NonTheorySymbolFinder;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.solverbuilder.SolverBuilder;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.solverbuilder.SolverBuilder.ExternalSolver;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.solverbuilder.SolverBuilder.SolverMode;
import de.uni_freiburg.informatik.ultimate.lib.srparse.LiteralUtils;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.PatternType;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.PatternType.ReqPeas;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.pea2boogie.CddToSmt;
import de.uni_freiburg.informatik.ultimate.pea2boogie.IReqSymbolTable;
import de.uni_freiburg.informatik.ultimate.pea2boogie.PeaResultUtil;
import de.uni_freiburg.informatik.ultimate.pea2boogie.generator.MusEnumerator.MusEnumeratorResult;
import de.uni_freiburg.informatik.ultimate.pea2boogie.preferences.Pea2BoogiePreferences.CompleteRtInconsistencyCheckMode;
import de.uni_freiburg.informatik.ultimate.util.datastructures.UnionFind;

/**
 * Implements the complete rt-inconsistency check for real-time requirements as described in
 * "A Practical and Complete Method for Detecting rt-Inconsistencies in Real-Time Requirements" (Hauff et al., REFSQ
 * 2026).
 *
 * The method consists of two steps:
 * <ol>
 * <li>Candidate extraction: compute all minimal weakly rt-inconsistent subsets by grouping non-violation conditions
 * (NVCs) by shared symbols and enumerating minimal unsatisfiable subsets (MUSes) within each group.</li>
 * <li>Contextual rt-inconsistency check: for each candidate, check whether it is contextually rt-inconsistent with
 * respect to the full set of requirements (delegated to the existing tool chain).</li>
 * </ol>
 *
 * The MUS enumeration can be configured via {@link CompleteRtInconsistencyCheckMode}.
 */
public class CompleteRtInconsistencyCheck {
	private final CddToSmtPreCheck mCddToSmtPreCheck;
	private final Script mScript;
	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;
	private final CompleteRtInconsistencyCheckMode mMode;
	private final Map<String, AnnotatedReq> mAnnotatedReqs;

	/**
	 * A requirement annotated with its critical phases for rt-inconsistency analysis.
	 *
	 * @param name
	 *            name of the requirement
	 * @param patternType
	 *            pattern type of the requirement
	 * @param counterTrace
	 *            countertrace representation of the requirement
	 * @param pea
	 *            phase event automaton of the requirement
	 * @param critPhases
	 *            map from critical phase index to {@link CritPhase}; a critical phase is a phase in which a violation of
	 *            the requirement can become unavoidable by any extension of the interpretation segment
	 */
	private record AnnotatedReq(String name, PatternType<?> patternType, CounterTrace counterTrace,
			PhaseEventAutomata pea, Map<Integer, CritPhase> critPhases) {
	}

	/**
	 * A critical phase of a requirement, used for weak rt-inconsistency checking.
	 *
	 * @param reqName
	 *            name of the requirement this critical phase belongs to
	 * @param index
	 *            phase index of this critical phase within the requirement's countertrace
	 * @param invariant
	 *            invariant (state expression) of the critical phase, used for the satisfiability condition Φ
	 * @param nvc
	 *            non-violation condition of the critical phase; specifies a valuation on observables that prevents
	 *            reaching the last phase of the requirement, used for the unsatisfiability condition Ψ
	 * @param seeping
	 *            whether this critical phase was derived via seeping through multiple subsequent phases
	 * @param symbols
	 *            non-theory symbols occurring in the non-violation condition, used for grouping NVCs by shared symbols
	 */
	private record CritPhase(String reqName, Integer index, Term invariant, Term nvc, boolean seeping,
			Set<NonTheorySymbol<?>> symbols) {
		public CritPhase(final String reqName, final Integer index, final Term invariant, final Term nvc,
				final boolean seeping) {
			this(reqName, index, invariant, nvc, seeping, new NonTheorySymbolFinder().findNonTheorySymbols(nvc));
		}
	}

	/**
	 * An element of a minimal unsatisfiable subset (MUS), identifying a critical phase that contributes to the
	 * unsatisfiability of a group of non-violation conditions.
	 *
	 * @param reqName
	 *            name of the requirement
	 * @param critPhaseIndex
	 *            index of the critical phase within the requirement
	 * @param seeping
	 *            whether the critical phase was derived via seeping
	 */
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

		mAnnotatedReqs = new HashMap<>();
		for (final var reqPea : reqPeas) {
			for (final Entry<CounterTrace, PhaseEventAutomata> e : reqPea.getCounterTrace2Pea()) {
				mAnnotatedReqs.put(e.getValue().getName(), new AnnotatedReq(e.getValue().getName(), reqPea.getPattern(),
						e.getKey(), e.getValue(), computeCritPhases(e.getKey(), e.getValue().getName())));
			}
		}
	}

	public List<Entry<PatternType<?>, PhaseEventAutomata>[]> check() {
		final List<AnnotatedReq> annotatedReqsList = new ArrayList<>(mAnnotatedReqs.values());
		final Set<Set<CritPhase>> groups = groupNvcsBySymbols(annotatedReqsList);

		final Set<Set<MusElement>> muses = new HashSet<>();
		for (final var group : groups) {
			if (group.size() <= 1) {
				continue;
			}

			mLogger.info("Enumerate muses of nvc group size: " + group.size());
			final List<CritPhase> sortedGroup =
					group.stream().sorted(Comparator.comparing(CritPhase::reqName).thenComparing(CritPhase::index))
							.collect(Collectors.toList());

			muses.addAll(enumerateMusesMarco(new ArrayList<>(sortedGroup)));
		}
		mLogger.info("Size of nvc muses: " + muses.size());

		muses.removeIf(e -> hasUnsatCritPhases(e, mAnnotatedReqs));
		mLogger.info("Size of nvc muses after filtering unsat crit phases: " + muses.size());

		muses.removeIf(e -> !hasLowerTimeBound(e, mAnnotatedReqs));
		mLogger.info("Size of nvc muses after filtering lower time bound: " + muses.size());

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
					annotatedReqs.get(musElement.reqName()).critPhases().get(musElement.critPhaseIndex()).invariant);
		}

		return LBool.UNSAT == SmtUtils.checkSatTerm(mScript, SmtUtils.and(mScript, critPhaseInvariants));
	}

	private static boolean hasLowerTimeBound(final Set<MusElement> musElements,
			final Map<String, AnnotatedReq> annotatedReqs) {

		return musElements.stream()
				.flatMap(
						musElement -> Arrays.stream(annotatedReqs.get(musElement.reqName()).counterTrace().getPhases()))
				.anyMatch(dcPhase -> (dcPhase.getBoundType() == CounterTrace.BOUND_GREATER
						|| dcPhase.getBoundType() == CounterTrace.BOUND_GREATEREQUAL));
	}

	private Map<Integer, CritPhase> computeCritPhases(final CounterTrace counterTrace, final String reqName) {
		final Map<Integer, CritPhase> results = new HashMap<>();

		final DCPhase[] phases = counterTrace.getPhases();
		final List<Term> seepInvariants = new ArrayList<>(Arrays.asList(mScript.term("true")));

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
				results.put(i, new CritPhase(reqName, i, invariant, SmtUtils.not(mScript, seepInvariants.getLast()),
						results.size() > 0));
				seepInvariants.add(seepInvariant);
			} else {
				// Found a critical phase with lower bound.
				if (mScript.getTheory().mTrue == SmtUtils.implies(mScript, invariant, seepInvariants.getLast())) {
					results.put(i,
							new CritPhase(reqName, i, invariant, SmtUtils.not(mScript, invariant), results.size() > 0));
				} else {
					results.put(i, new CritPhase(reqName, i, invariant, SmtUtils.not(mScript, seepInvariants.getLast()),
							results.size() > 0));
				}

				break;
			}
		}

		return results;
	}

	private Set<Set<CritPhase>> groupNvcsBySymbols(final List<AnnotatedReq> annotatedReqs) {
		final List<CritPhase> critPhases =
				annotatedReqs.stream().flatMap(ar -> ar.critPhases().values().stream()).collect(Collectors.toList());

		final UnionFind<CritPhase> unionFind = new UnionFind<>();
		for (final var critPhase : critPhases) {
			unionFind.makeEquivalenceClass(critPhase);
		}

		// Map each symbol to the list of critPhases that contain it
		final Map<NonTheorySymbol<?>, List<CritPhase>> symbolToCritPhases = new HashMap<>();
		for (final var critPhase : critPhases) {
			for (final var symbol : critPhase.symbols()) {
				symbolToCritPhases.computeIfAbsent(symbol, k -> new ArrayList<>()).add(critPhase);
			}
		}

		// Union critPhases that share a symbol
		for (final var phases : symbolToCritPhases.values()) {
			assert !phases.isEmpty();
			unionFind.union(phases);
		}

		return new HashSet<>(unionFind.getAllEquivalenceClasses());
	}

	/**
	 * Enumerates minimal unsatisfiable subsets (MUSes) using the unoptimized basic variant of the MARCO algorithm,
	 * implemented in Java with two Z3 solver instances.
	 *
	 * @see MusEnumerator
	 */
	private Set<Set<MusElement>> enumerateMusesMarco(final List<CritPhase> critPhases) {
		final Script scriptSubsetSolver = SolverBuilder.buildAndInitializeSolver(mServices,
				SolverBuilder.constructSolverSettings().setSolverMode(SolverMode.External_ModelsAndUnsatCoreMode)
						.setUseExternalSolver(ExternalSolver.Z3),
				"SubsetSolver");

		final Script scriptMapSolver = SolverBuilder.buildAndInitializeSolver(mServices,
				SolverBuilder.constructSolverSettings().setSolverMode(SolverMode.External_ModelsMode)
						.setUseExternalSolver(ExternalSolver.Z3),
				"MapSolver");

		final TermTransferrer termTransferrer =
				new TermTransferrer(mScript, new HistoryRecordingScript(scriptSubsetSolver));
		final List<Term> constraints = critPhases.stream().map(critPhase -> termTransferrer.transform(critPhase.nvc))
				.collect(Collectors.toList());

		final List<MusEnumeratorResult> musResults =
				MusEnumerator.enumerate(scriptSubsetSolver, scriptMapSolver, constraints, mLogger);
		scriptSubsetSolver.exit();
		scriptMapSolver.exit();

		final Set<Set<MusElement>> result =
				musResults.stream().filter(musResult -> musResult.type() == MusEnumeratorResult.Type.MUS)
						.map(musResult -> musResult.indices().stream().map(critPhases::get)
								.map(critPhase -> new MusElement(critPhase.reqName, critPhase.index, critPhase.seeping))
								.collect(Collectors.toSet()))
						.collect(Collectors.toSet());

		return result;
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
}
