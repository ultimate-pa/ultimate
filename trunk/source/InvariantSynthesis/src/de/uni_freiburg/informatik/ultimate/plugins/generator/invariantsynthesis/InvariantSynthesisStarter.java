/*
 * Copyright (C) 2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2017 Dennis Wölfing
 * Copyright (C) 2015-2017 University of Freiburg
 *
 * This file is part of the ULTIMATE InvariantSynthesis plug-in.
 *
 * The ULTIMATE InvariantSynthesis plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE InvariantSynthesis plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE InvariantSynthesis plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE InvariantSynthesis plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE InvariantSynthesis plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.invariantsynthesis;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Function;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.lib.results.AllSpecificationsHoldResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.DangerInvariantResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.GenericResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.PositiveResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.StatisticsResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.UnprovabilityReason;
import de.uni_freiburg.informatik.ultimate.core.lib.results.UnprovableResult;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.results.IResult;
import de.uni_freiburg.informatik.ultimate.core.model.results.IResultWithSeverity.Severity;
import de.uni_freiburg.informatik.ultimate.core.model.services.IBacktranslationService;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IcfgProgramExecution;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IcfgUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgElement;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.dangerinvariants.DangerInvariantUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateUnifier;
import de.uni_freiburg.informatik.ultimate.lib.proofs.PrePostConditionSpecification;
import de.uni_freiburg.informatik.ultimate.lib.proofs.ProofAnnotation;
import de.uni_freiburg.informatik.ultimate.lib.proofs.floydhoare.FloydHoareMapping;
import de.uni_freiburg.informatik.ultimate.lib.proofs.floydhoare.FloydHoareUtils;
import de.uni_freiburg.informatik.ultimate.lib.proofs.floydhoare.IcfgFloydHoareValidityCheck;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.IncrementalPlicationChecker.Validity;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.solverbuilder.SolverBuilder;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.solverbuilder.SolverBuilder.ExternalSolver;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.solverbuilder.SolverBuilder.SolverMode;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.solverbuilder.SolverBuilder.SolverSettings;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.plugins.generator.invariantsynthesis.preferences.InvariantSynthesisPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.invariantsynthesis.preferences.InvariantSynthesisPreferenceInitializer.IncreasingStrategy;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.AbstractCegarLoop.Result;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.pathinvariants.InvariantSynthesisSettings;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.pathinvariants.internal.AbstractTemplateIncreasingDimensionsStrategy;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.pathinvariants.internal.AggressiveTemplateIncreasingDimensionsStrategy;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.pathinvariants.internal.CFGInvariantsGenerator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.pathinvariants.internal.ConjunctsPriorizedTemplateIncreasingDimensionsStrategy;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.pathinvariants.internal.ConservativeTemplateIncreasingDimensionsStrategy;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.pathinvariants.internal.DangerInvariantGuesser;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.pathinvariants.internal.DefaultTemplateIncreasingDimensionsStrategy;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.pathinvariants.internal.DisjunctsWithBoundTemplateIncreasingDimensionsStrategy;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.pathinvariants.internal.ExponentialConjunctsTemplateIncreasingDimensionsStrategy;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.pathinvariants.internal.KindOfInvariant;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.pathinvariants.internal.MediumTemplateIncreasingDimensionsStrategy;
import de.uni_freiburg.informatik.ultimate.util.statistics.IStatisticsDataProvider;
import de.uni_freiburg.informatik.ultimate.util.statistics.StatisticsData;

public class InvariantSynthesisStarter<L extends IIcfgTransition<?>> {

	private final ILogger mLogger;
	private final IUltimateServiceProvider mServices;

	/**
	 * Root Node of this Ultimate model. I use this to store information that should be passed to the next plugin. The
	 * Successors of this node exactly the initial nodes of procedures.
	 */
	private final IElement mRootOfNewModel;
	private Result mOverallResult;
	private IElement mArtifact;

	public InvariantSynthesisStarter(final IUltimateServiceProvider services, final IIcfg<IcfgLocation> icfg) {
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(Activator.PLUGIN_ID);

		final SimplificationTechnique simplificationTechnique = SimplificationTechnique.SIMPLIFY_DDA;
		final XnfConversionTechnique xnfConversionTechnique =
				XnfConversionTechnique.BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION;
		final ManagedScript mgdScript = icfg.getCfgSmtToolkit().getManagedScript();
		final PredicateFactory predicateFactory =
				new PredicateFactory(mServices, mgdScript, icfg.getCfgSmtToolkit().getSymbolTable());
		final IPredicateUnifier predicateUnifier = new PredicateUnifier(mLogger, mServices, mgdScript, predicateFactory,
				icfg.getCfgSmtToolkit().getSymbolTable(), simplificationTechnique, xnfConversionTechnique);

		final InvariantSynthesisSettings invSynthSettings = constructSettings(icfg.getIdentifier());

		final IPreferenceProvider prefs = mServices.getPreferenceProvider(Activator.PLUGIN_ID);
		final KindOfInvariant kindOfInvariant =
				prefs.getEnum(InvariantSynthesisPreferenceInitializer.LABEL_KIND_INVARIANT, KindOfInvariant.class);

		final IPredicate predicateOfInitialLocations;
		final IPredicate predicateOfErrorLocations;

		if (kindOfInvariant == KindOfInvariant.DANGER) {
			predicateOfInitialLocations = predicateUnifier.getFalsePredicate();
			predicateOfErrorLocations = predicateUnifier.getTruePredicate();
		} else {
			assert kindOfInvariant == KindOfInvariant.SAFETY;
			predicateOfInitialLocations = predicateUnifier.getTruePredicate();
			predicateOfErrorLocations = predicateUnifier.getFalsePredicate();
		}

		final boolean guessDangerInvariant =
				prefs.getBoolean(InvariantSynthesisPreferenceInitializer.LABEL_DANGER_INVARIANT_GUESSING);
		if (kindOfInvariant == KindOfInvariant.DANGER && guessDangerInvariant) {
			final DangerInvariantGuesser dig = new DangerInvariantGuesser(icfg, services, predicateOfInitialLocations,
					predicateFactory, predicateUnifier, icfg.getCfgSmtToolkit());
			mLogger.info("Constructed danger invariant candidate");
			if (dig.isDangerInvariant()) {
				mLogger.info("Candidate is a valid danger invariant");
				mOverallResult = Result.UNSAFE;
				reportDangerResults(dig.getCandidateInvariant(), IcfgUtils.getErrorLocations(icfg),
						mServices.getBacktranslationService());
			} else {
				mLogger.info("Candidate is not a danger invariant");
				mOverallResult = Result.UNKNOWN;
				final String message = "Did not find a danger invariant";
				reportResult(new GenericResult(Activator.PLUGIN_ID, message, message, Severity.WARNING));
			}
			mRootOfNewModel = null;
			return;
		}

		final FloydHoareMapping<IcfgLocation> floydHoare;
		final CFGInvariantsGenerator cfgInvGenerator =
				new CFGInvariantsGenerator(icfg, services, predicateOfInitialLocations, predicateOfErrorLocations,
						predicateFactory, predicateUnifier, invSynthSettings, icfg.getCfgSmtToolkit(), kindOfInvariant);
		final Map<IcfgLocation, IPredicate> invariants = cfgInvGenerator.synthesizeInvariants();
		final IStatisticsDataProvider statistics = cfgInvGenerator.getInvariantSynthesisStatistics();
		if (invariants != null) {
			if (kindOfInvariant == KindOfInvariant.DANGER) {
				final Validity validity = DangerInvariantUtils.checkDangerInvariant(invariants, icfg, mgdScript,
						mServices, predicateFactory, mLogger);
				if (validity == Validity.VALID) {
					mOverallResult = Result.UNSAFE;
				} else {
					mLogger.warn("Danger invariant could not be confirmed to be correct: " + validity);
					mLogger.debug(invariants);
					mOverallResult = Result.UNKNOWN;
				}
				floydHoare = null;
			} else {
				assert kindOfInvariant == KindOfInvariant.SAFETY;

				final var initials = icfg.getInitialNodes().stream()
						.collect(Collectors.toMap(Function.identity(), l -> predicateOfInitialLocations));
				floydHoare = new FloydHoareMapping<>(
						PrePostConditionSpecification.forIcfg(icfg, initials, predicateOfErrorLocations), invariants);
				FloydHoareUtils.writeHoareAnnotationToLogger(icfg, floydHoare, mLogger, true);

				// Annotate the ICFG with the computed Floyd-Hoare annotation, so it can be consumed by other plugins.
				ProofAnnotation.addProof(icfg, floydHoare);

				mOverallResult = Result.SAFE;
			}
		} else {
			mOverallResult = Result.UNKNOWN;
			floydHoare = null;
		}

		final Map<String, Set<IcfgLocation>> proc2errNodes = icfg.getProcedureErrorNodes();
		final Collection<IcfgLocation> errNodesOfAllProc = new ArrayList<>();
		for (final Collection<IcfgLocation> errNodeOfProc : proc2errNodes.values()) {
			errNodesOfAllProc.addAll(errNodeOfProc);
		}

		if (mOverallResult == Result.SAFE) {
			final AllSpecificationsHoldResult result = AllSpecificationsHoldResult
					.createAllSpecificationsHoldResult(Activator.PLUGIN_NAME, errNodesOfAllProc.size());
			reportResult(result);
		}

		mLogger.debug("Overall result: " + mOverallResult);
		mLogger.debug("Continue processing: " + mServices.getProgressMonitorService().continueProcessing());
		if (mOverallResult == Result.SAFE) {
			assert floydHoare != null;
			assert new IcfgFloydHoareValidityCheck<>(services, icfg, floydHoare, true)
					.getResult() : "incorrect Hoare annotation";

			final IBacktranslationService backTranslatorService = mServices.getBacktranslationService();
			FloydHoareUtils.createInvariantResults(Activator.PLUGIN_NAME, icfg, floydHoare, backTranslatorService,
					this::reportResult);
			FloydHoareUtils.createProcedureContractResults(mServices, Activator.PLUGIN_NAME, icfg, floydHoare,
					backTranslatorService, this::reportResult);
		}
		final StatisticsData stat = new StatisticsData();
		stat.aggregateBenchmarkData(statistics);
		final IResult benchmarkResult =
				new StatisticsResult<>(Activator.PLUGIN_ID, "InvariantSynthesisStatistics", stat);
		reportResult(benchmarkResult);
		switch (mOverallResult) {
		case SAFE:
			reportPositiveResults(errNodesOfAllProc);
			break;
		case UNSAFE:
			reportDangerResults(invariants, IcfgUtils.getErrorLocations(icfg), mServices.getBacktranslationService());
			break;
		case TIMEOUT:
			throw new AssertionError();
		case UNKNOWN:
			mLogger.warn("Unable to infer correctness proof.");
			break;
		default:
			throw new UnsupportedOperationException("Unknown overall result " + mOverallResult);
		}

		mRootOfNewModel = mArtifact;
	}

	private InvariantSynthesisSettings constructSettings(final String cfgIdentifier) {
		final IPreferenceProvider prefs = mServices.getPreferenceProvider(Activator.PLUGIN_ID);

		final boolean useNonlinearConstraints =
				prefs.getBoolean(InvariantSynthesisPreferenceInitializer.LABEL_NONLINEAR_CONSTRAINTS);
		final boolean useExternalSolver =
				prefs.getBoolean(InvariantSynthesisPreferenceInitializer.LABEL_EXTERNAL_SMT_SOLVER);
		final long timeoutInMsSmtInterpol =
				prefs.getInt(InvariantSynthesisPreferenceInitializer.LABEL_SOLVER_TIMEOUT) * 1000;

		// TODO 2017-05-01 Matthias: Add settings if used more often.
		final boolean fakeNonIncrementalScript = false;
		final boolean dumpSmtScriptToFile = false;
		final String pathOfDumpedScript = "dump/";
		final String baseNameOfDumpedScript =
				useNonlinearConstraints ? "Nonlinear" + "_" + cfgIdentifier : "Linear" + "_" + cfgIdentifier;

		// DD 2019-10-29: These solver settings were only used with SolverMode.External_DefaultMode, in
		// LinearInequalityInvariantPatternProcessorFactory#produceSmtSolver()
		SolverSettings solverSettings = SolverBuilder.constructSolverSettings()
				.setSolverMode(SolverMode.External_DefaultMode).setUseFakeIncrementalScript(fakeNonIncrementalScript)
				.setSmtInterpolTimeout(timeoutInMsSmtInterpol)
				.setDumpSmtScriptToFile(dumpSmtScriptToFile, pathOfDumpedScript, baseNameOfDumpedScript, false);
		if (useExternalSolver) {
			// solverCommand = "yices-smt2 --incremental";
			// commandExternalSolver = "yices-smt2 --incremental -t " + timeoutSmtInterpol;
			// solverCommand = "/home/matthias/ultimate/barcelogic/barcelogic-NIRA -tlimit 5";
			final long externalSolverTimeout = timeoutInMsSmtInterpol;
			solverSettings = solverSettings.setUseExternalSolver(ExternalSolver.Z3, externalSolverTimeout);
		}

		final boolean useUnsatCores = prefs.getBoolean(InvariantSynthesisPreferenceInitializer.LABEL_UNSAT_CORES);
		final boolean useLBE = prefs.getBoolean(InvariantSynthesisPreferenceInitializer.LABEL_LARGE_BLOCK_ENCODING);
		final boolean useAbstractInterpretationPredicates =
				prefs.getBoolean(InvariantSynthesisPreferenceInitializer.LABEL_USE_ABSTRACT_INTERPRETATION);
		final boolean useWPForPathInvariants = false;

		final int initialDisjuncts = 1;// prefs.getInt(InvariantSynthesisPreferenceInitializer.LABEL_INITIAL_DISJUNCTS);
		final int disjunctsStep = 1;// prefs.getInt(InvariantSynthesisPreferenceInitializer.LABEL_STEP_DISJUNCTS);
		final int initialConjuncts = 3;// prefs.getInt(InvariantSynthesisPreferenceInitializer.LABEL_INITIAL_CONJUNCTS);
		final int conjunctsStep = 1;// prefs.getInt(InvariantSynthesisPreferenceInitializer.LABEL_STEP_CONJUNCTS);

		AbstractTemplateIncreasingDimensionsStrategy templateIncrDimensionsStrat = null;
		final IncreasingStrategy incrStrat = prefs.getEnum(InvariantSynthesisPreferenceInitializer.LABEL_INCR_STRATEGY,
				InvariantSynthesisPreferenceInitializer.DEF_INCR_STRATEGY, IncreasingStrategy.class);
		if (incrStrat == IncreasingStrategy.Conservative) {
			templateIncrDimensionsStrat = new ConservativeTemplateIncreasingDimensionsStrategy(initialDisjuncts,
					initialConjuncts, disjunctsStep, conjunctsStep);
		} else if (incrStrat == IncreasingStrategy.Medium) {
			templateIncrDimensionsStrat = new MediumTemplateIncreasingDimensionsStrategy(initialDisjuncts,
					initialConjuncts, disjunctsStep, conjunctsStep);
		} else if (incrStrat == IncreasingStrategy.IncrOnlyConjunctsAfterMaxDisjuncts) {
			templateIncrDimensionsStrat = new DisjunctsWithBoundTemplateIncreasingDimensionsStrategy(initialDisjuncts,
					initialConjuncts, disjunctsStep, conjunctsStep);
		} else if (incrStrat == IncreasingStrategy.Aggressive) {
			templateIncrDimensionsStrat = new AggressiveTemplateIncreasingDimensionsStrategy(initialDisjuncts,
					initialConjuncts, disjunctsStep, conjunctsStep);
		} else if (incrStrat == IncreasingStrategy.ExponentialConjuncts) {
			templateIncrDimensionsStrat = new ExponentialConjunctsTemplateIncreasingDimensionsStrategy(initialDisjuncts,
					initialConjuncts, disjunctsStep, conjunctsStep);
		} else if (incrStrat == IncreasingStrategy.ConjunctsPriorized) {
			templateIncrDimensionsStrat = new ConjunctsPriorizedTemplateIncreasingDimensionsStrategy(initialDisjuncts,
					initialConjuncts, disjunctsStep, conjunctsStep);
		} else {
			templateIncrDimensionsStrat = new DefaultTemplateIncreasingDimensionsStrategy(initialDisjuncts,
					initialConjuncts, disjunctsStep, conjunctsStep);
		}

		return new InvariantSynthesisSettings(solverSettings, templateIncrDimensionsStrat, useNonlinearConstraints,
				useUnsatCores, useAbstractInterpretationPredicates, useWPForPathInvariants, useLBE);
	}

	private void reportDangerResults(final Map<IcfgLocation, IPredicate> invariants,
			final Set<IcfgLocation> errorLocations, final IBacktranslationService backtranslator) {
		final Map<IcfgLocation, Term> map = new HashMap<>();
		for (final Map.Entry<IcfgLocation, IPredicate> entry : invariants.entrySet()) {
			map.put(entry.getKey(), entry.getValue().getFormula());
		}
		reportResult(new DangerInvariantResult<>(Activator.PLUGIN_NAME, map, errorLocations, backtranslator));
	}

	private void reportPositiveResults(final Collection<IcfgLocation> errorLocs) {
		for (final IcfgLocation errorLoc : errorLocs) {
			final PositiveResult<IIcfgElement> pResult =
					new PositiveResult<>(Activator.PLUGIN_NAME, errorLoc, mServices.getBacktranslationService());
			reportResult(pResult);
		}
	}

	private void reportUnproveableResult(final IcfgProgramExecution<L> pe,
			final List<UnprovabilityReason> unproabilityReasons) {
		final IcfgLocation errorPP = getErrorPP(pe);
		reportResult(new UnprovableResult<>(Activator.PLUGIN_NAME, errorPP, mServices.getBacktranslationService(), pe,
				unproabilityReasons));
	}

	private void reportResult(final IResult res) {
		mServices.getResultService().reportResult(Activator.PLUGIN_ID, res);
	}

	/**
	 * @return the root of the CFG.
	 */
	public IElement getRootOfNewModel() {
		return mRootOfNewModel;
	}

	public static <L extends IIcfgTransition<?>> IcfgLocation
			getErrorPP(final IcfgProgramExecution<L> rcfgProgramExecution) {
		final int lastPosition = rcfgProgramExecution.getLength() - 1;
		final IIcfgTransition<?> last = rcfgProgramExecution.getTraceElement(lastPosition).getTraceElement();
		return last.getTarget();
	}
}
