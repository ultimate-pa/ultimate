/*
 * Copyright (C) 2026 University of Freiburg
 *
 * This file is part of the ULTIMATE TraceAbstraction plug-in.
 *
 * The ULTIMATE TraceAbstraction plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TraceAbstraction plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceAbstraction plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceAbstraction plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TraceAbstraction plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.parallel;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.concurrent.atomic.AtomicBoolean;
import java.util.function.BooleanSupplier;
import java.util.function.Supplier;
import java.util.regex.Pattern;
import java.util.stream.Stream;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.VpAlphabet;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SubTermFinder;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.solverbuilder.SolverBuilder;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.solverbuilder.SolverBuilder.SolverMode;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.solverbuilder.SolverBuilder.SolverSettings;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfgbuilder.preferences.IcfgPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.parallel.WorkerThreadResult.WorkerType;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.TaCheckAndRefinementPreferences;

/**
 * The solver settings of the scripts of the workers, of k-induction and of the invariant supplier, for
 * {@link ParallelNwaCegarLoop} and the sequential {@code NwaCegarLoopWithKInduction}.
 *
 * @author Max Barth (max.barth@lmu.de)
 */
public final class WorkerSolverSettings {
	/**
	 * The solver of k-induction and the invariant supplier for a program that bitwuzla rejects although it is
	 * configured, see
	 * {@link #externalSolverCommand(TAPreferences, ILogger, WorkerType, BooleanSupplier, AtomicBoolean)}. The command
	 * of the SV-COMP integer settings.
	 */
	private static final String Z3_FOR_INT_AND_REAL = "z3 SMTLIB2_COMPLIANT=true -memory:2024 -smt2 -in";

	/**
	 * The per-check timeout option of the external solvers we can configure, by the name of their executable: the
	 * pattern matches the option as it may already appear in the configured command, the format string writes a new
	 * one. Mirrors {@link SolverBuilder.ExternalSolver}, which spells the same options for its built-in commands.
	 */
	private static final Map<String, Entry<Pattern, String>> SOLVER_TIMEOUT_OPTION =
			Map.of("z3", Map.entry(Pattern.compile("\\s*-t:\\d+"), " -t:%d"), "cvc4",
					Map.entry(Pattern.compile("\\s*--tlimit-per=\\d+"), " --tlimit-per=%d"), "cvc5",
					Map.entry(Pattern.compile("\\s*--tlimit-per=\\d+"), " --tlimit-per=%d"),
					// -t and --time-limit are bitwuzla's limit for the whole run, not per check, so they stay.
					"bitwuzla",
					Map.entry(Pattern.compile("\\s*(?:-T\\s*|--time-limit-per[=\\s]+)\\d+"), " --time-limit-per=%d"));

	/**
	 * The solver settings of one worker script. Which preference page describes the solver depends on the worker:
	 * <ul>
	 * <li>A TA worker's script plays the part of the main thread's CFG script: weakest preconditions, quantifier
	 * elimination, the predicate unifier and the Hoare triple checks run on it, while its trace checks get their own
	 * solver from the TraceAbstraction page via {@link TaCheckAndRefinementPreferences}. So it reads IcfgBuilder's
	 * page, like the CFG script of the sequential loop. (With the TraceAbstraction page, the SV-COMP bitvector settings
	 * ran all of that on bitwuzla without a per-query timeout, and computing backward predicates took about 20 times as
	 * long as in the sequential loop.)</li>
	 * <li>k-induction and the invariant supplier ask every query on their script, so they read the TraceAbstraction
	 * page: a user who configures a solver for TraceAbstraction expects that solver there. (IcfgBuilder's per-query
	 * timeout used to silently turn the proofs of a long-running k-induction worker into {@code unknown}.)</li>
	 * </ul>
	 *
	 * @param services
	 *            the services of the worker
	 * @param pref
	 *            the TraceAbstraction preferences
	 * @param workerType
	 *            the kind of worker this script is for; {@link WorkerType#KINDUCTION} may carry its own per-query
	 *            timeout, see {@link TraceAbstractionPreferenceInitializer#LABEL_KINDUCTION_SOLVER_TIMEOUT}.
	 * @param externalSolverCommand
	 *            the solver command of a worker that is no TA worker, see
	 *            {@link #externalSolverCommand(TAPreferences, ILogger, WorkerType, BooleanSupplier, AtomicBoolean)}
	 * @param filename
	 *            base name for a dumped SMT script
	 */
	public static SolverSettings getSolverSettings(final IUltimateServiceProvider services, final TAPreferences pref,
			final WorkerType workerType, final Supplier<String> externalSolverCommand, final String filename) {

		// The two benchmark-dump flags exist only on IcfgBuilder's page, so every worker reads them there.
		final IPreferenceProvider taPrefs = services.getPreferenceProvider(Activator.PLUGIN_ID);
		final IPreferenceProvider icfgPrefs = services.getPreferenceProvider(
				de.uni_freiburg.informatik.ultimate.plugins.generator.icfgbuilder.Activator.PLUGIN_ID);
		final IPreferenceProvider solverPrefs = workerType == WorkerType.TA ? icfgPrefs : taPrefs;

		final SolverMode solverMode;
		final String commandExternalSolver;
		final Logics logicForExternalSolver;
		if (workerType == WorkerType.TA) {
			solverMode = icfgPrefs.getEnum(IcfgPreferenceInitializer.LABEL_SOLVER, SolverMode.class);
			commandExternalSolver = icfgPrefs.getString(IcfgPreferenceInitializer.LABEL_EXT_SOLVER_COMMAND);
			logicForExternalSolver =
					Logics.valueOf(icfgPrefs.getString(IcfgPreferenceInitializer.LABEL_EXT_SOLVER_LOGIC));
		} else {
			solverMode = solverMode(pref, workerType);
			commandExternalSolver = externalSolverCommand.get();
			logicForExternalSolver = pref.logicForExternalSolver();
		}

		final boolean fakeNonIncrementalScript =
				solverPrefs.getBoolean(IcfgPreferenceInitializer.LABEL_FAKE_NON_INCREMENTAL_SCRIPT);

		final boolean dumpSmtScriptToFile = pref.dumpSmtScriptToFile();
		final boolean compressSmtScript = pref.compressDumpedSmtScript();
		final String pathOfDumpedScript = pref.pathOfDumpedScript();

		final boolean dumpUnsatCoreTrackBenchmark =
				icfgPrefs.getBoolean(IcfgPreferenceInitializer.LABEL_DUMP_UNSAT_CORE_BENCHMARK);

		final boolean dumpMainTrackBenchmark =
				icfgPrefs.getBoolean(IcfgPreferenceInitializer.LABEL_DUMP_MAIN_TRACK_BENCHMARK);

		final Map<String, String> additionalSmtOptions =
				solverPrefs.getKeyValueMap(IcfgPreferenceInitializer.LABEL_ADDITIONAL_SMT_OPTIONS);
		final SolverSettings solverSettings =
				SolverBuilder.constructSolverSettings().setUseFakeIncrementalScript(fakeNonIncrementalScript)
						// The worker type in the name: workers started in the same iteration would otherwise dump into
						// the same file and garble each other's script.
						.setDumpSmtScriptToFile(dumpSmtScriptToFile, pathOfDumpedScript, filename + workerType,
								compressSmtScript)
						.setDumpUnsatCoreTrackBenchmark(dumpUnsatCoreTrackBenchmark)
						.setDumpMainTrackBenchmark(dumpMainTrackBenchmark)
						.setUseExternalSolver(true, commandExternalSolver, logicForExternalSolver)
						.setSolverMode(solverMode).setAdditionalOptions(additionalSmtOptions);

		return solverSettings;
	}

	/**
	 * The solver mode of a worker's solver. k-induction only asks for satisfiability and models, never for an unsat
	 * core, so its solver does not produce them: cvc4 1.8 in incremental mode segfaults on the counterexample
	 * reconstruction's queries when unsat cores are enabled, and without them answers the very same script.
	 */
	private static SolverMode solverMode(final TAPreferences pref, final WorkerType workerType) {
		final SolverMode configured = pref.solverMode();
		if (workerType == WorkerType.KINDUCTION && configured == SolverMode.External_ModelsAndUnsatCoreMode) {
			return SolverMode.External_ModelsMode;
		}
		return configured;
	}

	/**
	 * The external solver command for a worker, with the k-induction per-query timeout applied if one is configured and
	 * this is a k-induction worker.
	 *
	 * @param bitwuzlaRejectsProgram
	 *            whether the program has a term bitwuzla rejects, only asked if bitwuzla is the configured solver
	 * @param loggedZ3InsteadOfBitwuzla
	 *            whether the replacement of bitwuzla by z3 was logged already; set when it is logged
	 */
	public static String externalSolverCommand(final TAPreferences pref, final ILogger logger,
			final WorkerType workerType, final BooleanSupplier bitwuzlaRejectsProgram,
			final AtomicBoolean loggedZ3InsteadOfBitwuzla) {
		String command = pref.commandExternalSolver().trim();
		// k-induction and the invariant supplier ask every query on this one solver. Unlike a trace check, which falls
		// back to the next solver of its strategy, they crash on the first query bitwuzla rejects.
		if ((workerType == WorkerType.KINDUCTION || workerType == WorkerType.INVARIANT)
				&& "bitwuzla".equals(executableName(command)) && bitwuzlaRejectsProgram.getAsBoolean()) {
			if (!loggedZ3InsteadOfBitwuzla.getAndSet(true)) {
				logger.info("The program has Int or Real terms that bitwuzla does not support, e.g. a negative "
						+ "floating-point constant; k-induction and the invariant supplier use \"%s\" instead of "
						+ "\"%s\"", Z3_FOR_INT_AND_REAL, command);
			}
			command = Z3_FOR_INT_AND_REAL;
		}
		final int timeout = pref.getKInductionSolverTimeout();
		if (workerType != WorkerType.KINDUCTION || timeout < 0) {
			// Inherit whatever the configured command says.
			return command;
		}
		final String executable = command.split("\\s+", 2)[0];
		final Entry<Pattern, String> option =
				SOLVER_TIMEOUT_OPTION.get(executable.substring(executable.lastIndexOf('/') + 1));
		if (option == null) {
			throw new UnsupportedOperationException("A k-induction SMT timeout of " + timeout
					+ "ms was configured, but we do not know the per-query timeout option of \"" + executable
					+ "\". Encode the timeout in the solver command instead, or use one of "
					+ SOLVER_TIMEOUT_OPTION.keySet() + ".");
		}
		// Drop any timeout the command already carries, so the k-induction setting wins rather than silently
		// losing to it.
		return option.getKey().matcher(command).replaceAll("").trim() + String.format(option.getValue(), timeout);
	}

	/**
	 * @return whether some letter of {@code alphabet} has a term that bitwuzla rejects, see
	 *         {@link #bitwuzlaRejects(Term)}
	 */
	public static boolean bitwuzlaRejectsProgram(final VpAlphabet<? extends IIcfgTransition<?>> alphabet) {
		return Stream.of(alphabet.getInternalAlphabet(), alphabet.getCallAlphabet(), alphabet.getReturnAlphabet())
				.flatMap(Set::stream).map(letter -> letter.getTransformula().getFormula()).anyMatch(
						formula -> !SubTermFinder.find(formula, WorkerSolverSettings::bitwuzlaRejects, true).isEmpty());
	}

	/**
	 * Bitwuzla knows neither Int nor Real. It only reads a non-negative number as the argument of {@code to_fp}, which
	 * is how the C translation writes a floating-point constant, even in a bit-precise program. A negative one is
	 * printed as {@code ((_ to_fp 11 53) rm (- 1.0))}, and bitwuzla answers "undefined symbol '-'".
	 */
	private static boolean bitwuzlaRejects(final Term term) {
		final String sort = term.getSort().getName();
		if (!SmtSortUtils.INT_SORT.equals(sort) && !SmtSortUtils.REAL_SORT.equals(sort)) {
			return false;
		}
		return !(term instanceof final ConstantTerm constant) || isNegative(constant.getValue());
	}

	private static boolean isNegative(final Object value) {
		if (value instanceof final BigInteger integer) {
			return integer.signum() < 0;
		}
		if (value instanceof final BigDecimal decimal) {
			return decimal.signum() < 0;
		}
		if (value instanceof final Rational rational) {
			return rational.isNegative();
		}
		return true;
	}

	/** @return whether {@code command} runs z3 */
	static boolean isZ3(final String command) {
		return "z3".equals(executableName(command));
	}

	private static String executableName(final String command) {
		final String executable = command.split("\\s+", 2)[0];
		return executable.substring(executable.lastIndexOf('/') + 1);
	}

	private WorkerSolverSettings() {
		// static methods only
	}
}
