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
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.srparse.LiteralUtils;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.PatternType;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.PatternType.ReqPeas;
import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.Annotation;
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
import de.uni_freiburg.informatik.ultimate.smtinterpol.muses.MusContainer;
import de.uni_freiburg.informatik.ultimate.smtinterpol.muses.MusEnumerationScript;
import de.uni_freiburg.informatik.ultimate.smtinterpol.muses.MusOptions;
import de.uni_freiburg.informatik.ultimate.smtinterpol.muses.Translator;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.SMTInterpol;

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

	private record CritPhase(Integer index, Term invariant, Term nvc, boolean seeping) {
	}

	private record MusElement(String reqName, Integer critPhaseIndex, boolean seeping) {
	}

	public RtInconsistencyPreCheckMus(final List<ReqPeas> reqPeas, final PeaResultUtil peaResultUtil,
			final Boogie2SMT boogie2Smt,
			final BoogieDeclarations boogieDeclarations, final IReqSymbolTable reqSymbolTable, final Script script,
			final ManagedScript managedScript, final IUltimateServiceProvider services, final ILogger logger) {

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
						e.getKey(), e.getValue(), identifyCritPhases(e.getKey())));
			}
		}
	}

	public List<Entry<PatternType<?>, PhaseEventAutomata>[]> check() {
		final Set<Set<MusElement>> muses = enumerateNvcMuses(new ArrayList<>(mAnnotatedReqs.values()));
		mLogger.info("Size of nvc muses: " + muses.size());

		muses.removeIf(e -> hasUnsatCritPhases(e, mAnnotatedReqs));
		mLogger.info("Size of nvc muses after filtering unsat crit phases: " + muses.size());

		muses.removeIf(e -> !hasTimeBound(e, mAnnotatedReqs));
		mLogger.info("Size of nvc muses after filtering time bound: " + muses.size());

		mLogger.info("Muses: " + muses);

		final Set<Set<String>> uniqueMuses = muses.stream()
				.map(inner -> inner.stream()
						.map(s -> s.reqName())
						.collect(Collectors.toSet()))
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
			critPhaseInvariants
			.add(annotatedReqs.get(musElement.reqName()).critPhases()
					.get(musElement.critPhaseIndex()).invariant);
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

	private Set<Set<MusElement>> enumerateNvcMuses(final List<AnnotatedReq> annotatedReqs) {
		Set<Set<MusElement>> result = new HashSet<>();

		final SMTInterpol smtInterpol = new SMTInterpol();
		smtInterpol.setOption(SMTLIBConstants.PRODUCE_UNSAT_CORES, true);
		smtInterpol.setLogic(Logics.ALL);

		final MusEnumerationScript musEnumerationScript = new MusEnumerationScript(smtInterpol);
		musEnumerationScript.setOption(MusOptions.LOG_ADDITIONAL_INFORMATION, false);
		musEnumerationScript.setOption(SMTLIBConstants.RANDOM_SEED, 0);

		final TermTransferrer termTransferrer =
				new TermTransferrer(mScript, new HistoryRecordingScript(musEnumerationScript));

		for (final var annotatedReq : annotatedReqs) {
			annotatedReq.critPhases().forEach((phaseIndex, critPhase) -> {
				final String name = annotatedReq.name() + "_" + phaseIndex + (critPhase.seeping ? "s" : "");

				musEnumerationScript
				.assertTerm(musEnumerationScript.annotate(termTransferrer.transform(critPhase.nvc),
						new Annotation(":named", name)));

				mLogger.info(String.format("Assert nvc for mus enumeration: %s %s", name, critPhase.nvc));
			});
		}

		final LBool sat = musEnumerationScript.checkSat();
		mLogger.info("Check sat of all nvcs: " + sat);

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

	private Map<Integer, CritPhase> identifyCritPhases(final CounterTrace counterTrace) {
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
}