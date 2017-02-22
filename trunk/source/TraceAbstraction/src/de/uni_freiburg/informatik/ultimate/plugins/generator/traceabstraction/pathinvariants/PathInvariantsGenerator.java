/*
 * Copyright (C) 2015 Dirk Steinmetz
 * Copyright (C) 2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
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
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
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

package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.pathinvariants;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Objects;
import java.util.Set;
import java.util.SortedMap;
import java.util.function.Function;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.automata.Word;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IProgressAwareTimer;
import de.uni_freiburg.informatik.ultimate.core.model.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.IcfgUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IInternalAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgInternalTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocationIterator;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.TransFormulaBuilder;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.PartialQuantifierElimination;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SolverBuilder.Settings;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.linearTerms.PrenexNormalForm;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.PredicateTransformer;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.livevariable.LiveVariableState;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.tool.AbstractInterpreter;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.tool.IAbstractInterpretationResult;
import de.uni_freiburg.informatik.ultimate.plugins.blockencoding.BlockEncoder;
import de.uni_freiburg.informatik.ultimate.plugins.blockencoding.preferences.BlockEncodingPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.blockencoding.preferences.BlockEncodingPreferences.MinimizeStates;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.PathProgram;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.CoverageAnalysis.BackwardCoveringInformation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.pathinvariants.NonInductiveAnnotationGenerator.Approximation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.pathinvariants.internal.AbstractLinearInvariantPattern;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.pathinvariants.internal.AllProgramVariablesStrategy;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.pathinvariants.internal.CFGInvariantsGenerator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.pathinvariants.internal.DynamicPatternSettingsStrategy;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.pathinvariants.internal.DynamicPatternSettingsStrategyWithBounds;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.pathinvariants.internal.DynamicPatternSettingsStrategyWithGlobalTemplateLevel;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.pathinvariants.internal.IInvariantPatternProcessor;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.pathinvariants.internal.IInvariantPatternProcessorFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.pathinvariants.internal.ILinearInequalityInvariantPatternStrategy;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.pathinvariants.internal.LinearInequalityInvariantPatternProcessorFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.pathinvariants.internal.LiveVariablesStrategy;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.pathinvariants.internal.PathInvariantsStatisticsGenerator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.pathinvariants.internal.VarsInUnsatCoreStrategy;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.ISLPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.AssertCodeBlockOrder;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.InterpolationTechnique;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.UnsatCores;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.IInterpolantGenerator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.InterpolantComputationStatus;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.InterpolantComputationStatus.ItpErrorStatus;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.TraceCheckerSpWp;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.TraceCheckerUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;
import de.uni_freiburg.informatik.ultimate.util.statistics.AStatisticsType;
import de.uni_freiburg.informatik.ultimate.util.statistics.IStatisticsElement;

/**
 * Represents a map of invariants to a run that has been generated using a {@link IInvariantPatternProcessor} on the
 * run-projected CFG.
 *
 * @author Dirk Steinmetz, Matthias Heizmann, Betim Musa
 */
public final class PathInvariantsGenerator implements IInterpolantGenerator {

	// Indicates whether the predicates from the weakest precondition are added to the constraints or not.
	private final boolean mUseWeakestPrecondition;
	// There are two different ways to add an additional predicate to the invariant templates/patterns.
	// 1. We add the predicate to each disjunct as an additional conjunct, or
	// 2. we add the predicate as an additional disjunct.
	private static final boolean ADD_WP_TO_EACH_CONJUNCT = true;

	private static final boolean USE_UNSAT_CORES_FOR_DYNAMIC_PATTERN_CHANGES = true;
	private static final boolean USE_DYNAMIC_PATTERN_WITH_BOUNDS = false;

	/**
	 * @see {@link DynamicPatternSettingsStrategyWithGlobalTemplateLevel}
	 */
	private static final boolean USE_DYNAMIC_PATTERN_CHANGES_WITH_GLOBAL_TEMPLATE_LEVEL = false;

	private static final boolean USE_UNDER_APPROX_FOR_MAX_CONJUNCTS = false;
	private static final boolean USE_OVER_APPROX_FOR_MIN_DISJUNCTS = false;

	/**
	 * If set to true, we always construct two copies of each invariant pattern, one strict inequality and one
	 * non-strict inequality. If set to false we use only one non-strict inequality.
	 */
	private static final boolean ALWAYS_STRICT_AND_NON_STRICT_COPIES = false;
	/**
	 * If a template contains more than 1 conjunct, then use alternatingly strict and non-strict inequalities. I.e. the
	 * even conjuncts are strict whereas the odd conjuncts are non-strict inequalities.
	 */
	private static final boolean USE_STRICT_INEQUALITIES_ALTERNATINGLY = false;
	/**
	 * Transform the path program by applying large block encoding. Synthesize invariants only for the large block
	 * encoded program and use less expensive techniques to obtain the remaining invariants.
	 */
	private static final boolean APPLY_LARGE_BLOCK_ENCODING = true;

	private static final boolean DEBUG_OUTPUT_GENERALLY_ALLOWED = true;
	// DEBUG_OUTPUT_I is used for status updates, e.g. which part of invariant synthesis is active, what is the sat-result of the constraints
	private static boolean DEBUG_OUTPUT_I = true;
	// DEBUG_OUTPUT_II is used for output with higher time complexity, like size of constraints
	private static boolean DEBUG_OUTPUT_II = true;

	private static final int MAX_ROUNDS = Integer.MAX_VALUE;

	private final boolean mUseLiveVariables;

	private final NestedRun<? extends IAction, IPredicate> mRun;
	private final IPredicate mPrecondition;
	private final IPredicate mPostcondition;
	private final IPredicate[] mInterpolants;
	private final IPredicateUnifier mPredicateUnifier;
	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;
	private final PredicateTransformer mPredicateTransformer;
	private final InterpolantComputationStatus mInterpolantComputationStatus;
	private final IToolchainStorage mStorage;
	private final IAbstractInterpretationResult<LiveVariableState<IcfgEdge>, IcfgEdge, IProgramVarOrConst, IcfgLocation> mAbstractInterpretationResult;
	private final boolean mUseAbstractInterpretationPredicates;
	private final PathInvariantsStatisticsGenerator mPathInvariantsStats;

	/**
	 * Generates a map of invariants to a given run, using an {@link IInvariantPatternProcessor} produced by the default
	 * {@link IInvariantPatternProcessorFactory} (with default settings).
	 *
	 * @param services
	 *            Service provider to use, for example for logging and timeouts
	 * @param storage
	 *            IToolchainstorage of the current Ultimate toolchain.
	 * @param run
	 *            an infeasible run to project into a CFG. Must only contain {@link ISLPredicate}s as states.
	 * @param precondition
	 *            the predicate to use for the first program point in the run
	 * @param postcondition
	 *            the predicate to use for the last program point in the run
	 * @param predicateUnifier
	 *            the predicate unifier to unify final predicates with
	 * @param icfg
	 * @param csToolkit
	 *            the smt manager for constructing the default {@link IInvariantPatternProcessorFactory}
	 * @param simplicationTechnique
	 * @param xnfConversionTechnique
	 */
	public PathInvariantsGenerator(final IUltimateServiceProvider services, final IToolchainStorage storage,
			final NestedRun<? extends IAction, IPredicate> run, final IPredicate precondition,
			final IPredicate postcondition, final IPredicateUnifier predicateUnifier, final IIcfg<?> icfg,
			final boolean useNonlinearConstraints, final boolean useUnsatCores, final boolean useLiveVariables,
			final boolean useAbstractInterpretationPredicates, final boolean useWPForPathInvariants,
			final Settings solverSettings, final SimplificationTechnique simplificationTechnique,
			final XnfConversionTechnique xnfConversionTechnique) {
		mServices = services;
		mRun = run;
		mStorage = storage;
		mPrecondition = precondition;
		mPostcondition = postcondition;
		mPredicateUnifier = predicateUnifier;
		mPredicateTransformer = new PredicateTransformer(services, icfg.getCfgSmtToolkit().getManagedScript(),
				simplificationTechnique, xnfConversionTechnique);
		mUseLiveVariables = useLiveVariables;
		mUseWeakestPrecondition = useWPForPathInvariants;
		mUseAbstractInterpretationPredicates = useAbstractInterpretationPredicates;

		mLogger = services.getLoggingService().getLogger(Activator.PLUGIN_ID);
		mPathInvariantsStats = new PathInvariantsStatisticsGenerator();
		if (!DEBUG_OUTPUT_GENERALLY_ALLOWED) {
			DEBUG_OUTPUT_I = false;
			DEBUG_OUTPUT_II = false;
		}
		if (DEBUG_OUTPUT_I) {
			mLogger.info("Current run: " + run);
		}
		final Set<? extends IcfgEdge> allowedTransitions = extractTransitionsFromRun(run);

		final IIcfg<IcfgLocation> pathProgram =
				new PathProgram<>("PathInvariantsPathProgram", icfg, allowedTransitions);
		/**
		 * Map that assigns to each large block encoded icfg location the corresponding location in the orginal icfg
		 */
		Map<IcfgLocation, IcfgLocation> lbeBacktranslation = null;
		final IIcfg<IcfgLocation> lbePathProgram;
		if (APPLY_LARGE_BLOCK_ENCODING) {
			final IUltimateServiceProvider beServices =
					services.registerPreferenceLayer(getClass(), BlockEncodingPreferences.PLUGIN_ID);
			final IPreferenceProvider ups = beServices.getPreferenceProvider(BlockEncodingPreferences.PLUGIN_ID);
			ups.put(BlockEncodingPreferences.FXP_INTERPROCEDURAL_COMPOSITION, false);
			ups.put(BlockEncodingPreferences.FXP_MINIMIZE_STATES, MinimizeStates.MULTI);
			// TODO: If you remove infeasible edges, you may end up with an empty program. Either disable this or deal
			// with it.
			ups.put(BlockEncodingPreferences.FXP_REMOVE_INFEASIBLE_EDGES, false);
			final BlockEncoder blockEncoder = new BlockEncoder(mLogger, beServices, pathProgram,
					SimplificationTechnique.SIMPLIFY_DDA, XnfConversionTechnique.BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION);
			lbePathProgram = blockEncoder.getResult();
			assert !lbePathProgram.getInitialNodes().isEmpty() : "LBE ICFG is emtpy";
			lbeBacktranslation = blockEncoder.getBacktranslator().getLocationMapping();
		} else {
			lbePathProgram = pathProgram;
		}
		if (mUseLiveVariables || mUseAbstractInterpretationPredicates) {
			mAbstractInterpretationResult = applyAbstractInterpretationOnPathProgram(lbePathProgram);
		} else {
			mAbstractInterpretationResult = null;
		}

		// Map<IcfgLocation, IPredicate> invariants = generatePathInvariants(useVarsFromUnsatCore, icfg,
		// simplificationTechnique, xnfConversionTechnique, solverSettings, useNonlinerConstraints);
		Map<IcfgLocation, IPredicate> invariants =
				generateInvariantsForPathProgram(useUnsatCores, icfg, lbePathProgram, simplificationTechnique,
						xnfConversionTechnique, solverSettings, useNonlinearConstraints);
		if (invariants != null) {
			if (APPLY_LARGE_BLOCK_ENCODING) {
				invariants = computeIntermediateInvariants(pathProgram, invariants, lbeBacktranslation,
						predicateUnifier, icfg.getCfgSmtToolkit());
			}
			// Populate resulting array
			mInterpolants = new IPredicate[mRun.getLength()];
			for (int i = 0; i < mRun.getLength(); i++) {
				final IcfgLocation locFromRun = ((ISLPredicate) mRun.getStateAtPosition(i)).getProgramPoint();
				final IcfgLocation locFromPathProgram =
						invariants.keySet().stream().filter(loc -> loc.toString().endsWith(locFromRun.toString()))
						.collect(Collectors.toList()).get(0);
				mInterpolants[i] = invariants.get(locFromPathProgram);
				if (DEBUG_OUTPUT_I) {
					mLogger.info("Interpolant no " + i + " " + mInterpolants[i].toString());
				}
			}
			if (DEBUG_OUTPUT_I) {
				mLogger.info("Invariants found and " + "processed.");
				mLogger.info("Got a Invariant map of length " + mInterpolants.length);
			}
			mInterpolantComputationStatus = new InterpolantComputationStatus(true, null, null);
		} else {
			mInterpolants = null;
			if (DEBUG_OUTPUT_I) {
				mLogger.info("No invariants found.");
			}
			mInterpolantComputationStatus =
					new InterpolantComputationStatus(false, ItpErrorStatus.ALGORITHM_FAILED, null);
		}
	}

	/**
	 * Given invariants for an LBE encoded {@link Icfg}, compute invariants for the original {@link Icfg} by filling the
	 * gaps using interpolation or an SP-based workaround.
	 * 
	 * @param inputIcfg
	 *            {@link Icfg} for which we want to compute invariants.
	 * @param lbeInvariants
	 *            Invariants of an {@link Icfg} that was obtained by large block encoding.
	 * @param lbeBacktranslation
	 *            Backtranslation from {@link IcfgLocation}s of the LBE {@link Icfg} to inputIcfg.
	 * @return An invariant mapping for input icfg.
	 */
	private Map<IcfgLocation, IPredicate> computeIntermediateInvariants(final IIcfg<IcfgLocation> inputIcfg,
			final Map<IcfgLocation, IPredicate> lbeInvariants, final Map<IcfgLocation, IcfgLocation> lbeBacktranslation,
			final IPredicateUnifier predicateUnifier, final CfgSmtToolkit csToolkit) {
		// add invariants for non-intermedicate locations directly
		final Map<IcfgLocation, IPredicate> resultInvariantMapping = new HashMap<>();
		for (final Entry<IcfgLocation, IPredicate> entry : lbeInvariants.entrySet()) {
			resultInvariantMapping.put(lbeBacktranslation.get(entry.getKey()), entry.getValue());
		}

		// try to add intermediate invariants using interpolation
		for (final IcfgLocation lbeLoc : lbeInvariants.keySet()) {
			final IcfgLocation origLoc = lbeBacktranslation.get(lbeLoc);
			if (!origLoc.getOutgoingEdges().isEmpty()) {
				tryToAddInvariantsUsingInterpolation(origLoc, resultInvariantMapping, predicateUnifier, csToolkit);
			}
		}
		final Set<IcfgLocation> inputIcfgLocations = extractAllIcfgLocations(inputIcfg);
		if (DEBUG_OUTPUT_I) {
			mLogger.info("path program has " + inputIcfgLocations.size() + " locations");
			mLogger.info(lbeInvariants.size() + " invariants obtained by synthesis");
			mLogger.info(resultInvariantMapping.size() - lbeInvariants.size() + " invariants obtained by interpolation");
		}
		int numberSpInvariants = 0;
		final ArrayDeque<IcfgLocation> inputIcfgLocationsWithoutInvariants = new ArrayDeque<>();
		for (final IcfgLocation loc : inputIcfgLocations) {
			if (!resultInvariantMapping.keySet().contains(loc)) {
				inputIcfgLocationsWithoutInvariants.add(loc);
			}
		}
		while (!inputIcfgLocationsWithoutInvariants.isEmpty()) {
			final IcfgLocation some = inputIcfgLocationsWithoutInvariants.removeFirst();
			if (allPredecessorsHaveInvariants(some, resultInvariantMapping)) {
				final IPredicate invar = computeInvariantUsingSp(some, resultInvariantMapping,
						csToolkit.getManagedScript(), predicateUnifier);
				resultInvariantMapping.put(some, invar);
				numberSpInvariants++;
			} else {
				inputIcfgLocationsWithoutInvariants.add(some);
			}
		}
		if (DEBUG_OUTPUT_I) {
			mLogger.info("remaining " + numberSpInvariants + " invariants computed via SP");
		}
		return resultInvariantMapping;
	}

	/**
	 * Check if loc has an outgoing run of branchless locations compute missing invariants along this runs using
	 * interpolation.
	 */
	private void tryToAddInvariantsUsingInterpolation(final IcfgLocation loc,
			final Map<IcfgLocation, IPredicate> invariants, final IPredicateUnifier predicateUnifier,
			final CfgSmtToolkit csToolkit) {
		final NestedRun<IAction, IcfgLocation> run = extractRunOfBranchlessLocs(loc, invariants.keySet());
		if (run == null) {
			return;
		}
		final IPredicate precondition = invariants.get(run.getStateAtPosition(0));
		final IPredicate postcondition = invariants.get(run.getStateAtPosition(run.getLength() - 1));
		final IPredicate[] interpolants =
				computeInterpolantsAlongRun(run, precondition, postcondition, predicateUnifier, csToolkit);
		for (int i = 1; i < run.getLength() - 1; i++) {
			invariants.put(run.getStateAtPosition(i), interpolants[i - 1]);
		}
	}

	/**
	 * @return set that contains all {@link IcfgLocation}s of an icfg.
	 */
	private static Set<IcfgLocation> extractAllIcfgLocations(final IIcfg<IcfgLocation> icfg) {
		final Set<IcfgLocation> result = new HashSet<>();
		final IcfgLocationIterator<?> iter = new IcfgLocationIterator<>(icfg);
		while (iter.hasNext()) {
			result.add(iter.next());
		}
		return result;
	}

	/**
	 * @return Invariant for {@link IcfgLocation} loc computed as the disjunction of the postconditions of the
	 *         invariants of all predecessor locations
	 */
	private IPredicate computeInvariantUsingSp(final IcfgLocation loc, final Map<IcfgLocation, IPredicate> invariants,
			final ManagedScript mgdScript, final IPredicateUnifier predicateUnifier) {
		final SimplificationTechnique simplificationTechnique = SimplificationTechnique.SIMPLIFY_DDA;
		final XnfConversionTechnique xnfConversionTechnique =
				XnfConversionTechnique.BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION;
		final PredicateTransformer pt =
				new PredicateTransformer(mServices, mgdScript, simplificationTechnique, xnfConversionTechnique);
		final List<Term> disjuncts = new ArrayList<>();
		for (final IcfgEdge edge : loc.getIncomingEdges()) {
			final IcfgLocation pred = edge.getSource();
			final IPredicate predInv = invariants.get(pred);
			final Term post = pt.strongestPostcondition(predInv, edge.getTransformula());
			disjuncts.add(post);
		}
		final Term disjunction = SmtUtils.or(mgdScript.getScript(), disjuncts);
		final IPredicate invar = predicateUnifier.getOrConstructPredicate(disjunction);
		return invar;
	}

	/**
	 * @return true iff each predecessors of loc is in the keySet of the invariants Map.
	 */
	private static boolean allPredecessorsHaveInvariants(final IcfgLocation loc,
			final Map<IcfgLocation, IPredicate> invariants) {
		for (final IcfgLocation pred : loc.getIncomingNodes()) {
			if (!invariants.containsKey(pred)) {
				return false;
			}
		}
		return true;
	}

	private IPredicate[] computeInterpolantsAlongRun(final NestedRun<IAction, IcfgLocation> run,
			final IPredicate precondition, final IPredicate postcondition, final IPredicateUnifier predicateUnifier,
			final CfgSmtToolkit csToolkit) {
		final SortedMap<Integer, IPredicate> pendingContexts = Collections.emptySortedMap();
		final AssertCodeBlockOrder assertCodeBlocksIncrementally = AssertCodeBlockOrder.NOT_INCREMENTALLY;
		final UnsatCores unsatCores = UnsatCores.CONJUNCT_LEVEL;
		final boolean useLiveVariables = true;
		final boolean computeRcfgProgramExecution = false;
		final InterpolationTechnique interpolation = InterpolationTechnique.ForwardPredicates;
		final ManagedScript mgdScriptTc = csToolkit.getManagedScript();
		final SimplificationTechnique simplificationTechnique = SimplificationTechnique.SIMPLIFY_DDA;
		final XnfConversionTechnique xnfConversionTechnique =
				XnfConversionTechnique.BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION;
		@SuppressWarnings("unchecked")
		final TraceCheckerSpWp tc = new TraceCheckerSpWp(precondition, postcondition, pendingContexts,
				(NestedWord<? extends IIcfgTransition<?>>) run.getWord(), csToolkit, assertCodeBlocksIncrementally,
				unsatCores, useLiveVariables, mServices, computeRcfgProgramExecution, predicateUnifier, interpolation,
				mgdScriptTc, xnfConversionTechnique, simplificationTechnique, run.getStateSequence());
		return tc.getInterpolants();
	}

	/**
	 * Try to construct a run (whose letters are {@link IAction}s and whose states are {@link IcfgLocation}) that starts
	 * in loc and ends in some element of goalLocs. Each intermediate {@link IcfgLocation} of the run must have exactly
	 * one predecessor and one successor. Return null if no such run exists.
	 */
	private static <T extends IAction> NestedRun<T, IcfgLocation> extractRunOfBranchlessLocs(final IcfgLocation loc,
			final Set<IcfgLocation> goalLocs) {
		NestedRun<T, IcfgLocation> run = new NestedRun<>(loc);
		IcfgLocation currentLoc = loc;
		while (true) {
			if (currentLoc.getOutgoingEdges().isEmpty()) {
				throw new AssertionError("no outgoing edge");
			} else if (currentLoc.getOutgoingEdges().size() == 1) {
				final IcfgEdge edge = currentLoc.getOutgoingEdges().get(0);
				@SuppressWarnings("unchecked")
				final NestedRun<T, IcfgLocation> suffix =
				new NestedRun<>(edge.getSource(), (T) edge, NestedWord.INTERNAL_POSITION, edge.getTarget());
				run = run.concatenate(suffix);
				currentLoc = edge.getTarget();
				if (goalLocs.contains(currentLoc)) {
					return run;
				}
				if (currentLoc.getIncomingEdges().size() > 1) {
					return null;
				}
			} else if (currentLoc.getOutgoingEdges().size() > 1) {
				return null;
			}
		}
	}

	/**
	 * Creates a default factory.
	 *
	 * @param services
	 *            Service provider to use, for example for logging and timeouts
	 * @param storage
	 *            IToolchainstorage of the current Ultimate toolchain.
	 * @param predicateUnifier
	 *            the predicate unifier to unify final predicates with
	 * @param csToolkit
	 *            the smt manager for constructing the default {@link IInvariantPatternProcessorFactory}
	 * @param simplicationTechnique
	 * @param xnfConversionTechnique
	 * @param axioms
	 * @return a default invariant pattern processor factory
	 */
	private static IInvariantPatternProcessorFactory<?> createDefaultFactory(final IUltimateServiceProvider services,
			final IToolchainStorage storage, final IPredicateUnifier predicateUnifier, final CfgSmtToolkit csToolkit,
			final boolean useNonlinerConstraints, final boolean useVarsFromUnsatCore, final Settings solverSettings,
			final SimplificationTechnique simplicationTechnique, final XnfConversionTechnique xnfConversionTechnique,
			final IPredicate axioms,
			final ILinearInequalityInvariantPatternStrategy<Collection<Collection<AbstractLinearInvariantPattern>>> strategy,
			final Map<IcfgLocation, UnmodifiableTransFormula> loc2underApprox,
			final Map<IcfgLocation, UnmodifiableTransFormula> loc2overApprox) {

		return new LinearInequalityInvariantPatternProcessorFactory(services, storage, predicateUnifier, csToolkit,
				strategy, useNonlinerConstraints, useVarsFromUnsatCore, solverSettings, simplicationTechnique, xnfConversionTechnique, axioms, loc2underApprox, loc2overApprox);
	}

	private static ILinearInequalityInvariantPatternStrategy<Collection<Collection<AbstractLinearInvariantPattern>>>
	getStrategy(final boolean useVarsFromUnsatCore, final boolean useLiveVars,
			final Set<IProgramVar> allProgramVariables,
			final Map<IcfgLocation, Set<IProgramVar>> locations2LiveVariables) {
		if (useVarsFromUnsatCore) {
			if (USE_UNSAT_CORES_FOR_DYNAMIC_PATTERN_CHANGES) {
				if (USE_DYNAMIC_PATTERN_WITH_BOUNDS) {
					return new DynamicPatternSettingsStrategyWithBounds(1, 1, 1, 1, MAX_ROUNDS, allProgramVariables,
							locations2LiveVariables, ALWAYS_STRICT_AND_NON_STRICT_COPIES,
							USE_STRICT_INEQUALITIES_ALTERNATINGLY);
				}
				if (USE_DYNAMIC_PATTERN_CHANGES_WITH_GLOBAL_TEMPLATE_LEVEL) {
					return new DynamicPatternSettingsStrategyWithGlobalTemplateLevel(1, 1, 1, 1, MAX_ROUNDS,
							allProgramVariables, locations2LiveVariables, ALWAYS_STRICT_AND_NON_STRICT_COPIES,
							USE_STRICT_INEQUALITIES_ALTERNATINGLY);
				}
				return new DynamicPatternSettingsStrategy(1, 1, 1, 1, MAX_ROUNDS, allProgramVariables,
						locations2LiveVariables, ALWAYS_STRICT_AND_NON_STRICT_COPIES,
						USE_STRICT_INEQUALITIES_ALTERNATINGLY);
			}
			return new VarsInUnsatCoreStrategy(1, 1, 1, 1, MAX_ROUNDS, allProgramVariables, locations2LiveVariables,
					ALWAYS_STRICT_AND_NON_STRICT_COPIES, USE_STRICT_INEQUALITIES_ALTERNATINGLY);
		} else if (useLiveVars) {
			return new LiveVariablesStrategy(1, 1, 1, 1, MAX_ROUNDS, allProgramVariables, locations2LiveVariables,
					ALWAYS_STRICT_AND_NON_STRICT_COPIES, USE_STRICT_INEQUALITIES_ALTERNATINGLY);
		}
		return new AllProgramVariablesStrategy(1, 1, 1, 1, MAX_ROUNDS, allProgramVariables, allProgramVariables,
				ALWAYS_STRICT_AND_NON_STRICT_COPIES, USE_STRICT_INEQUALITIES_ALTERNATINGLY);
	}

	/**
	 * Compute weakest precondition for those locations which are predecessors of the error locations and successors of
	 * any loop locations. If there are no loop locations, then we compute it only for the last two locations. TODO: If
	 * assertion is inside of a loop, then compute WP only for the last transition (i.e. the transition that reaches the
	 * error location).
	 *
	 * @param pathProgram
	 * @return
	 */
	private Map<IcfgLocation, UnmodifiableTransFormula> computeWPForPathProgram(final IIcfg<IcfgLocation> pathProgram,
			final ManagedScript managedScript) {
		final Set<IcfgLocation> loopLocations = pathProgram.getLoopLocations();
		final Set<IcfgLocation> locsOfNonEmptyLoops = extractLocationsOfNonEmptyLoops(pathProgram);
		final IcfgLocation errorloc = extractErrorLocationFromPathProgram(pathProgram);
		final Map<IcfgLocation, IPredicate> locs2WP = new HashMap<>();
		locs2WP.put(errorloc, mPostcondition);
		List<IcfgEdge> edges2visit = errorloc.getIncomingEdges();
		int levelCounter = 0;
		while (true) {
			final List<IcfgEdge> newEdges = new ArrayList<>();
			for (final IcfgEdge e : edges2visit) {
				if (!(e instanceof IInternalAction)) {
					throw new UnsupportedOperationException("interprocedural traces are not supported (yet)");
				}
				// Compute wp only if the source node is not an initial node
				if (!e.getSource().getIncomingEdges().isEmpty()) {
					// Compute WP for the formula of the current transition and the predicate at the target location.
					final Term wpTerm = mPredicateTransformer.weakestPrecondition(locs2WP.get(e.getTarget()),
							((IInternalAction) e).getTransformula());
					final Term wpTermWithoutQuantifiers = PartialQuantifierElimination.tryToEliminate(mServices,
							mLogger, managedScript, wpTerm, SimplificationTechnique.SIMPLIFY_DDA,
							XnfConversionTechnique.BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION);
					if (new PrenexNormalForm(managedScript)
							.transform(wpTermWithoutQuantifiers) instanceof QuantifiedFormula) {
						throw new UnsupportedOperationException("Quantifier elimination failed.");
					}
					final IPredicate wp = mPredicateUnifier.getOrConstructPredicate(wpTermWithoutQuantifiers);
					locs2WP.put(e.getSource(), wp);
					if (!locsOfNonEmptyLoops.contains(e.getSource()) || loopLocations.isEmpty() && levelCounter < 2) {
						newEdges.addAll(e.getSource().getIncomingEdges());
					}
				}
			}
			if (loopLocations.isEmpty()) {
				levelCounter++;
			}

			if (newEdges.isEmpty() || levelCounter >= 2) {
				break;
			}
			edges2visit = newEdges;

		}
		// remove the mapping (error-location -> false) from result
		locs2WP.remove(errorloc);

		return convertMapToPredsToMapToUnmodTrans(locs2WP, managedScript);
	}

	private static Map<IcfgLocation, UnmodifiableTransFormula> convertMapToPredsToMapToUnmodTrans(
			final Map<IcfgLocation, IPredicate> locs2Preds, final ManagedScript managedScript) {

		final Map<IcfgLocation, UnmodifiableTransFormula> result =
				locs2Preds.keySet().stream().collect(Collectors.toMap(loc -> loc, loc -> TransFormulaBuilder
						.constructTransFormulaFromPredicate(locs2Preds.get(loc), managedScript)));
		return result;
	}

	/**
	 * Check for each loop location of the path program if it contains some inner statements.
	 *
	 * @param pathProgram
	 * @return
	 */
	private static Set<IcfgLocation> extractLocationsOfNonEmptyLoops(final IIcfg<IcfgLocation> pathProgram) {
		final Set<IcfgLocation> loopLocations = pathProgram.getLoopLocations();
		final Set<IcfgLocation> locationsOfNonEmptyLoops = new HashSet<>(loopLocations.size());
		for (final IcfgLocation currLoc : loopLocations) {
			final List<IcfgEdge> outEdges = currLoc.getOutgoingEdges();
			// if (outEdges.isEmpty()) {
			// break;
			// }
			for (final IcfgEdge e : outEdges) {
				if (nodeIsReachable(currLoc, e)) {
					locationsOfNonEmptyLoops.add(currLoc);
					break;
				}
			}
		}
		return locationsOfNonEmptyLoops;
	}

	private static boolean nodeIsReachable(final IcfgLocation currLoc, final IcfgEdge e) {
		final Set<IcfgLocation> visitedNodes = new HashSet<>();
		final List<IcfgEdge> edgesToProcess = new LinkedList<>();
		edgesToProcess.add(e);
		while (!edgesToProcess.isEmpty()) {
			final IcfgEdge currEdge = edgesToProcess.remove(edgesToProcess.size() - 1);
			final IcfgLocation targ = currEdge.getTarget();
			if (Objects.equals(targ, currLoc)) {
				return true;
			} else if (!visitedNodes.contains(targ)) {
				visitedNodes.add(targ);
				edgesToProcess.addAll(targ.getOutgoingEdges());
			}
		}
		return false;
	}

	private Map<IcfgLocation, UnmodifiableTransFormula> extractAbstractInterpretationPredicates(
			final IAbstractInterpretationResult<LiveVariableState<IcfgEdge>, IcfgEdge, IProgramVarOrConst, IcfgLocation> abstractInterpretationResult,
			final ManagedScript managedScript) {
		final Map<IcfgLocation, UnmodifiableTransFormula> result = new HashMap<>();
		final Map<IcfgLocation, Term> locs2term = abstractInterpretationResult.getLoc2Term();
		final ArrayList<Term> termsAsList = new ArrayList<>(abstractInterpretationResult.getTerms());
		// If the only predicate found by Abstract Interpretation is 'true', then return the empty map, as the predicate
		// 'true' is not helpful.
		if (termsAsList.isEmpty() || termsAsList.size() == 1 && "true".equals(termsAsList.get(0).toString())) {
			return result;
		}
		for (final Map.Entry<IcfgLocation, Term> entry : locs2term.entrySet()) {
			result.put(entry.getKey(), TransFormulaBuilder.constructTransFormulaFromPredicate(
					mPredicateUnifier.getOrConstructPredicate(entry.getValue()), managedScript));
		}
		return result;
	}

	private static IcfgLocation extractErrorLocationFromPathProgram(final IIcfg<IcfgLocation> pathProgram) {
		final Set<IcfgLocation> errorLocs = IcfgUtils.getErrorLocations(pathProgram);
		assert errorLocs.size() == 1 : "There should be only one error location";
		return errorLocs.iterator().next();
	}

	private Map<IcfgLocation, IPredicate> generateInvariantsForPathProgram(final boolean useUnsatCores,
			final IIcfg<?> icfg, final IIcfg<IcfgLocation> pathProgram,
			final SimplificationTechnique simplificationTechnique, final XnfConversionTechnique xnfConversionTechnique,
			final Settings solverSettings, final boolean useNonlinearConstraints) {
		if (DEBUG_OUTPUT_I) {
			mLogger.info("Started with a run of length " + mRun.getLength());
		}

		final IcfgLocation startLocation = new ArrayList<>(pathProgram.getInitialNodes()).get(0);
		final IcfgLocation errorLocation = extractErrorLocationFromPathProgram(pathProgram);
		final List<IcfgLocation> locationsAsList = new ArrayList<>();
		final List<IcfgInternalTransition> transitionsAsList = new ArrayList<>();
		final Set<IProgramVar> allProgramVars = new HashSet<>();
		// Get locations, transitions and program variables from the path program
		extractLocationsTransitionsAndVariablesFromPathProgram(pathProgram, locationsAsList, transitionsAsList,
				allProgramVars);
		if (DEBUG_OUTPUT_I) {
			mLogger.info("Built projected CFG, " + locationsAsList.size() + " states and "
					+ transitionsAsList.size() + " transitions.");
		}
		Map<IcfgLocation, Set<IProgramVar>> pathprogramLocs2LiveVars = null;

		if (mUseLiveVariables || mUseAbstractInterpretationPredicates) {
			// pathprogramLocs2LiveVars = applyAbstractInterpretationOnPathProgram(pathProgram);
			assert mAbstractInterpretationResult != null : "Abstract Interpretation has not been applied on path program to"
					+ " generate live variables";
			final Map<IcfgLocation, LiveVariableState<IcfgEdge>> loc2states =
					mAbstractInterpretationResult.getLoc2SingleStates();
			pathprogramLocs2LiveVars = new HashMap<>();

			for (final Entry<IcfgLocation, LiveVariableState<IcfgEdge>> entry : loc2states.entrySet()) {
				pathprogramLocs2LiveVars.put(entry.getKey(), entry.getValue().getLiveVariablesAsProgramVars());
			}
			// At the initial location no variable is live
			pathprogramLocs2LiveVars.put(startLocation, new HashSet<IProgramVar>());
			if (DEBUG_OUTPUT_II) {
				mLogger.info("Live variables computed: " + pathprogramLocs2LiveVars);
			}
		}
		Map<IcfgLocation, UnmodifiableTransFormula> loc2underApprox = null;
		Map<IcfgLocation, UnmodifiableTransFormula> loc2overApprox = null;
		
		if (useUnsatCores) {
			// Compute under-/overapproximation only if we use unsat cores during invariant synthesis
			final NonInductiveAnnotationGenerator underApprox = new NonInductiveAnnotationGenerator(mServices,
					mPredicateUnifier.getPredicateFactory(), pathProgram, Approximation.UNDERAPPROXIMATION);
			final NonInductiveAnnotationGenerator overApprox = new NonInductiveAnnotationGenerator(mServices,
					mPredicateUnifier.getPredicateFactory(), pathProgram, Approximation.OVERAPPROXIMATION);

			loc2underApprox =
					convertHashRelation(underApprox.getResult(), icfg.getCfgSmtToolkit().getManagedScript());
			loc2overApprox =
					convertHashRelation(overApprox.getResult(), icfg.getCfgSmtToolkit().getManagedScript());
		}
		final Map<IcfgLocation, UnmodifiableTransFormula> pathprogramLocs2Predicates = new HashMap<>();
		if (mUseWeakestPrecondition) {
			pathprogramLocs2Predicates.putAll(loc2overApprox);
		}

		if (mUseAbstractInterpretationPredicates) {
			pathprogramLocs2Predicates.putAll(extractAbstractInterpretationPredicates(mAbstractInterpretationResult,
					icfg.getCfgSmtToolkit().getManagedScript()));
		}

		final ILinearInequalityInvariantPatternStrategy<Collection<Collection<AbstractLinearInvariantPattern>>> strategy =
				getStrategy(useUnsatCores, mUseLiveVariables, allProgramVars, pathprogramLocs2LiveVars);

		if (USE_UNDER_APPROX_FOR_MAX_CONJUNCTS) {
			for (final Map.Entry<IcfgLocation, UnmodifiableTransFormula> entry : loc2underApprox.entrySet()) {
				final List<Integer> maxDisjunctsMaxConjuncts =
						getDisjunctsAndConjunctsFromTerm(entry.getValue().getFormula());
				strategy.setNumOfConjunctsForLocation(entry.getKey(), maxDisjunctsMaxConjuncts.get(1));
			}
		} else if (USE_OVER_APPROX_FOR_MIN_DISJUNCTS) {
			for (final Map.Entry<IcfgLocation, UnmodifiableTransFormula> entry : loc2underApprox.entrySet()) {
				final List<Integer> maxDisjunctsMaxConjuncts =
						getDisjunctsAndConjunctsFromTerm(entry.getValue().getFormula());
				strategy.setNumOfDisjunctsForLocation(entry.getKey(), maxDisjunctsMaxConjuncts.get(0));
			}
		}
		final IInvariantPatternProcessorFactory<?> invPatternProcFactory = createDefaultFactory(mServices, mStorage,
				mPredicateUnifier, icfg.getCfgSmtToolkit(), useNonlinearConstraints, useUnsatCores,
				solverSettings, simplificationTechnique, xnfConversionTechnique, icfg.getCfgSmtToolkit().getAxioms(),
				strategy, loc2underApprox, loc2overApprox);

		// Generate invariants
		final CFGInvariantsGenerator generator = new CFGInvariantsGenerator(mServices, mPathInvariantsStats, DEBUG_OUTPUT_GENERALLY_ALLOWED);
		final Map<IcfgLocation, IPredicate> invariants;

		invariants = generator.generateInvariantsForTransitions(locationsAsList, transitionsAsList, mPrecondition,
				mPostcondition, startLocation, errorLocation, invPatternProcFactory, useUnsatCores,
				allProgramVars, pathprogramLocs2LiveVars, pathprogramLocs2Predicates,
				mUseWeakestPrecondition || mUseAbstractInterpretationPredicates, ADD_WP_TO_EACH_CONJUNCT);
		if (DEBUG_OUTPUT_I) {
			mLogger.info("Generated invariant map.");
		}

		return invariants;
	}

	private static Map<IcfgLocation, UnmodifiableTransFormula> convertHashRelation(
			final HashRelation<IcfgLocation, IPredicate> loc2SetOfPreds, final ManagedScript managedScript) {

		final Map<IcfgLocation, IPredicate> loc2Predicate = new HashMap<>(loc2SetOfPreds.getDomain().size());
		for (final IcfgLocation loc : loc2SetOfPreds.getDomain()) {
			final List<IPredicate> preds = new ArrayList<>(loc2SetOfPreds.getImage(loc).size());
			preds.addAll(loc2SetOfPreds.getImage(loc));
			// Currently, we use only one predicate
			loc2Predicate.put(loc, preds.get(0));
		}
		return convertMapToPredsToMapToUnmodTrans(loc2Predicate, managedScript);
	}

	private static void extractLocationsTransitionsAndVariablesFromPathProgram(final IIcfg<IcfgLocation> pathProgram,
			final List<IcfgLocation> locationsOfPP, final List<IcfgInternalTransition> transitionsOfPP,
			final Set<IProgramVar> allVariablesFromPP) {
		final LinkedList<IcfgLocation> locs2visit = new LinkedList<>();
		locs2visit.addAll(pathProgram.getInitialNodes());
		final LinkedHashSet<IcfgLocation> visitedLocs = new LinkedHashSet<>();
		final LinkedList<IcfgInternalTransition> edges = new LinkedList<>();
		while (!locs2visit.isEmpty()) {
			final IcfgLocation loc = locs2visit.removeFirst();
			if (visitedLocs.add(loc)) {
				for (final IcfgEdge e : loc.getOutgoingEdges()) {
					locs2visit.addLast(e.getTarget());
					if (!(e instanceof IInternalAction)) {
						throw new UnsupportedOperationException("interprocedural traces are not supported (yet)");
					}
					final UnmodifiableTransFormula tf = ((IInternalAction) e).getTransformula();
					allVariablesFromPP.addAll(tf.getInVars().keySet());
					allVariablesFromPP.addAll(tf.getOutVars().keySet());
					edges.addLast(new IcfgInternalTransition(e.getSource(), e.getTarget(), e.getPayload(), tf));
				}
			}
		}
		locationsOfPP.addAll(visitedLocs);
		transitionsOfPP.addAll(edges);
	}

	private static List<Integer> getDisjunctsAndConjunctsFromTerm(final Term term) {
		final List<Integer> result = new ArrayList<>(2);
		int maxNumOfConjuncts = 1;
		int maxNumOfDisjuncts = 1;
		final ArrayList<Term> termsToCheck = new ArrayList<>();
		termsToCheck.add(term);
		while (!termsToCheck.isEmpty()) {
			final Term t = termsToCheck.remove(0);
			if (t instanceof ApplicationTerm) {
				final ApplicationTerm at = (ApplicationTerm) t;
				if ("and".equals(at.getFunction().getName())) {
					if (at.getParameters().length > maxNumOfConjuncts) {
						maxNumOfConjuncts = at.getParameters().length;
					}
				} else if ("or".equals(at.getFunction().getName())) {
					if (at.getParameters().length > maxNumOfDisjuncts) {
						maxNumOfDisjuncts = at.getParameters().length;
					}
				}
				for (final Term param : at.getParameters()) {
					termsToCheck.add(param);
				}

			}
		}
		result.add(0, maxNumOfDisjuncts);
		result.add(1, maxNumOfConjuncts);
		return result;
	}

	// private List<IcfgLocation> extractLocationsFromPathProgram(IIcfg<IcfgLocation> pathProgram) {
	// LinkedList<IcfgLocation> locs2visit = new LinkedList<>();
	// locs2visit.addAll(pathProgram.getInitialNodes());
	// LinkedHashSet<IcfgLocation> visitedLocs = new LinkedHashSet<>();
	// while (!locs2visit.isEmpty()) {
	// IcfgLocation loc = locs2visit.removeFirst();
	// if (visitedLocs.add(loc)) {
	// for (IcfgEdge e : loc.getOutgoingEdges()) {
	// locs2visit.addLast(e.getTarget());
	// }
	// }
	// }
	//
	//
	// return new ArrayList<IcfgLocation>(visitedLocs);
	// }

	/**
	 * Computes for each location of the given path program a set of variables which are <emph> live </emph>.
	 *
	 * @param pathProgram
	 * @return
	 */
	private IAbstractInterpretationResult<LiveVariableState<IcfgEdge>, IcfgEdge, IProgramVarOrConst, IcfgLocation>
	applyAbstractInterpretationOnPathProgram(final IIcfg<IcfgLocation> pathProgram) {
		// allow for 20% of the remaining time
		final IProgressAwareTimer timer = mServices.getProgressMonitorService().getChildTimer(0.2);
		return AbstractInterpreter.runFutureLiveVariableDomain(pathProgram, timer, mServices, true, mLogger);
	}

	private static Set<? extends IcfgEdge>
	extractTransitionsFromRun(final NestedRun<? extends IAction, IPredicate> run) {
		final int len = run.getLength();
		final LinkedHashSet<IcfgInternalTransition> transitions = new LinkedHashSet<>(len - 1);
		IcfgLocation previousLocation = null;

		for (int i = 0; i < len; i++) {
			final ISLPredicate pred = (ISLPredicate) run.getStateAtPosition(i);
			final IcfgLocation currentLocation = pred.getProgramPoint();
			if (i > 0) {
				if (!run.getWord().isInternalPosition(i - 1)) {
					throw new UnsupportedOperationException("interprocedural traces are not supported (yet)");
				}
				final UnmodifiableTransFormula transFormula =
						((IInternalAction) run.getSymbol(i - 1)).getTransformula();
				transitions.add(new IcfgInternalTransition(previousLocation, currentLocation,
						currentLocation.getPayload(), transFormula));
			}
			previousLocation = currentLocation;
		}
		return transitions;
	}

	@Override
	public Word<? extends IAction> getTrace() {
		return mRun.getWord();
	}

	@Override
	public IPredicate getPrecondition() {
		return mPrecondition;
	}

	@Override
	public IPredicate getPostcondition() {
		return mPostcondition;
	}

	@Override
	public Map<Integer, IPredicate> getPendingContexts() {
		throw new UnsupportedOperationException("Call/Return not supported yet");
	}

	@Override
	public IPredicateUnifier getPredicateUnifier() {
		return mPredicateUnifier;
	}

	/**
	 * Returns a sequence of interpolants (see definition in {@link IInterpolantGenerator}) the trace which is
	 * mRun.getWord() with an additional property. If the ProgramPoint and position i and k coincide then the
	 * interpolants at position i and k coincide.
	 *
	 * @return sequence of interpolants according to the run provided in the constructor or null if no such sequence has
	 *         been found; without first interpolant (the precondition)
	 */
	@Override
	public IPredicate[] getInterpolants() {
		if (mInterpolants == null) {
			return null;
		}
		final IPredicate[] interpolantMapWithOutFirstInterpolant = new IPredicate[mInterpolants.length - 2];
		System.arraycopy(mInterpolants, 1, interpolantMapWithOutFirstInterpolant, 0, mInterpolants.length - 2);
		return interpolantMapWithOutFirstInterpolant;
	}

	@Override
	public boolean isPerfectSequence() {
		final BackwardCoveringInformation bci = TraceCheckerUtils.computeCoverageCapability(mServices, this, mLogger);
		final boolean isPerfect = bci.getPotentialBackwardCoverings() == bci.getSuccessfullBackwardCoverings();
		return isPerfect;
	}

	@Override
	public InterpolantComputationStatus getInterpolantComputationStatus() {
		return mInterpolantComputationStatus;
	}

	public PathInvariantsStatisticsGenerator getPathInvariantsBenchmarks() {
		return mPathInvariantsStats;
	}

	// Benchmarks Section
	@SuppressWarnings("squid:S00115")
	public enum PathInvariantsStatisticsDefinitions implements IStatisticsElement {
		// the sum of path program size (measured as the number of inequalities of all transformulas) for each overall
		// iteration
		ProgramSize(Integer.class, AStatisticsType.sIntegerAddition, AStatisticsType.sKeyBeforeData),
		// the sum of path program locations for each overall iteration
		ProgramLocs(Integer.class, AStatisticsType.sIntegerAddition, AStatisticsType.sKeyBeforeData),
		// the sum of path program variables for each overall iteration
		ProgramVars(Integer.class, AStatisticsType.sIntegerAddition, AStatisticsType.sKeyBeforeData),
		// the sum of template inequalities per location per round per iteration
		SumOfTemplateInequalities(Integer.class, AStatisticsType.sIntegerAddition, AStatisticsType.sKeyBeforeData),
		// the minimum size of all templates occurring in the most recent round
		SizeOfLargestTemplate(Integer.class, AStatisticsType.sIntegerMaximum, AStatisticsType.sKeyBeforeData),
		// the minimum size of all templates occurring in the most recent round
		SizeOfSmallestTemplate(Integer.class, AStatisticsType.sIntegerMaximum, AStatisticsType.sKeyBeforeData),
		// the maximum of the sum of template inequalities per round
		MaxNumOfInequalities(Integer.class, AStatisticsType.sIntegerMaximum, AStatisticsType.sKeyBeforeData),
		// the maximum number of rounds
		MaxRound(Integer.class, AStatisticsType.sIntegerMaximum, AStatisticsType.sKeyBeforeData),
		// the sum of variables per location per round
		SumVarsPerLoc(Integer.class, AStatisticsType.sIntegerAddition, AStatisticsType.sKeyBeforeData),
		// the sum of the difference of all variables and the live variables per location per round
		SumNonLiveVarsPerLoc(Integer.class, AStatisticsType.sIntegerAddition, AStatisticsType.sKeyBeforeData),
		// the sum of the difference of all variables and the variables from the unsat core per location per round
		SumNonUnsatCoreLocs(Integer.class, AStatisticsType.sIntegerAddition, AStatisticsType.sKeyBeforeData),
		// the sum of the difference of all variables and the variables from the unsat core per location per round
		SumNonUnsatCoreVars(Integer.class, AStatisticsType.sIntegerAddition, AStatisticsType.sKeyBeforeData),
		// the maximum DAG-size of (the sum of template inequalities per location per round) for normal constraints
		TreeSizeNormalConstr(Integer.class, AStatisticsType.sIntegerMaximum, AStatisticsType.sKeyBeforeData),
		// the maximum DAG-size of (the sum of template inequalities per location per round) for constraints of Under-
		// and/or Overapproximations
		TreeSizeApproxConstr(Integer.class, AStatisticsType.sIntegerMaximum, AStatisticsType.sKeyBeforeData),
		// Number of Motzkin Transformations for normal constraints
		MotzkinTransformationsNormalConstr(Integer.class, AStatisticsType.sIntegerAddition,
				AStatisticsType.sKeyBeforeData),
		// Number of Motzkin Transformations for constraints of Under- and/or Overapproximations
		MotzkinTransformationsApproxConstr(Integer.class, AStatisticsType.sIntegerAddition,
				AStatisticsType.sKeyBeforeData),
		// Number of Motzkin Coefficients needed for normal constraints
		MotzkinCoefficientsNormalConstr(Integer.class, AStatisticsType.sIntegerAddition,
				AStatisticsType.sKeyBeforeData),
		// Number of Motzkin Coefficients needed for constraints of Under- and/or Overapproximations
		MotzkinCoefficientsApproxConstr(Integer.class, AStatisticsType.sIntegerAddition,
				AStatisticsType.sKeyBeforeData),
		// the sum of the time needed per round to solve the constraints
		ConstraintsSolvingTime(Long.class, AStatisticsType.sLongAddition, AStatisticsType.sTimeBeforeKey),
		// the sum of the time needed per round to construct the constraints
		ConstraintsConstructionTime(Long.class, AStatisticsType.sLongAddition, AStatisticsType.sTimeBeforeKey),
		// Sat status
		SatStatus(String.class, s1 -> s2 -> new String((String) s1 + "; " + (String) s2),
				AStatisticsType.sKeyBeforeData);

		private final Class<?> mClazz;
		private final Function<Object, Function<Object, Object>> mAggr;
		private final Function<String, Function<Object, String>> mPrettyprinter;

		PathInvariantsStatisticsDefinitions(final Class<?> clazz, final Function<Object, Function<Object, Object>> aggr,
				final Function<String, Function<Object, String>> prettyprinter) {
			mClazz = clazz;
			mAggr = aggr;
			mPrettyprinter = prettyprinter;
		}

		@Override
		public Class<?> getDataType() {
			return mClazz;
		}

		@Override
		public Object aggregate(final Object o1, final Object o2) {
			return mAggr.apply(o1).apply(o2);
		}

		@Override
		public String prettyprint(final Object o) {
			return mPrettyprinter.apply(name()).apply(o);
		}

	}
}
