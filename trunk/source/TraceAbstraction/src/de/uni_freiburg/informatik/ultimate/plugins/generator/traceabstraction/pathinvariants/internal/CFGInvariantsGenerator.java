/*
 * Copyright (C) 2015 Dirk Steinmetz
 * Copyright (C) 2017 Betim Musa
 * Copyright (C) 2017 Dennis Wölfing
 * Copyright (C) 2015-2017 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.pathinvariants.internal;

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
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.ToolchainCanceledException;
import de.uni_freiburg.informatik.ultimate.core.lib.results.StatisticsResult;
import de.uni_freiburg.informatik.ultimate.core.model.results.IResult;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IProgressAwareTimer;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractInterpretationResult;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IcfgUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IInternalAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgInternalTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaBuilder;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SolverBuilder.SolverSettings;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.xnf.Dnf;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.livevariable.LiveVariableState;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.tool.AbstractInterpreter;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.pathinvariants.InvariantSynthesisSettings;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.pathinvariants.LargeBlockEncodingIcfgTransformer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.pathinvariants.NonInductiveAnnotationGenerator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.pathinvariants.NonInductiveAnnotationGenerator.Approximation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.pathinvariants.internal.LinearInequalityInvariantPatternProcessor.LinearInequalityPatternProcessorStatistics;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;
import de.uni_freiburg.informatik.ultimate.util.statistics.StatisticsData;

/**
 * Generate invariants for a given control-flow graph (CFG) using a constraint-based approach with on-demand template
 * selection. It executes the following steps:
 * <ol>
 * <li>(Optionally) Apply large-block encoding on the given CFG to retrieve a compact CFG.</li>
 * <li>Select a template using a {@link AbstractTemplateIncreasingDimensionsStrategy} for each node of the CFG.</li>
 * <li>Construct a constraint for each edge of the CFG.</li>
 * <li>Solve the constraints for the free parameters. If there is a solution, then build an inductive formula
 * (invariant) for each node of the CFG. Otherwise retry by going back to step 1.</li>
 * </ol>
 */
public final class CFGInvariantsGenerator {

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
	 * In practice we never have seen more than 5 rounds with a successful result, therefore we limit the maximal number
	 * of rounds to 10.
	 */
	private static final int MAX_ROUNDS = 10;

	private static final boolean USE_LIVE_VARIABLES = true;

	/**
	 * Report a {@link StatisticsResult} for every round.
	 */
	private static final boolean TEMPLATE_STATISTICS_MODE = true;

	private static boolean INIT_USE_EMPTY_PATTERNS = true;
	private static boolean USE_VARS_FROM_UNSAT_CORE_FOR_EACH_LOC = true;

	/**
	 * Transform the path program by applying large block encoding. Synthesize invariants only for the large block
	 * encoded program and use less expensive techniques to obtain the remaining invariants.
	 */
	private final boolean mApplyLargeBlockEncoding;

	private final ILogger mLogger;
	private final IUltimateServiceProvider mServices;

	private final PredicateFactory mPredicateFactory;
	private final IPredicateUnifier mPredicateUnifier;
	private final IPredicate mPredicateOfInitialLocations;
	private final IPredicate mPredicateOfErrorLocations;
	private final IIcfg<IcfgLocation> mIcfg;

	private final InvariantSynthesisStatisticsGenerator mPathInvariantsStatistics;
	private final Map<Integer, InvariantSynthesisStatisticsGenerator> mRound2InvariantSynthesisStatistics;
	private final InvariantSynthesisSettings mInvariantSynthesisSettings;
	private final CfgSmtToolkit mCsToolKit;
	private final KindOfInvariant mKindOfInvariant;

	public CFGInvariantsGenerator(final IIcfg<IcfgLocation> icfg, final IUltimateServiceProvider services,
			final IPredicate predicateOfInitialLocations, final IPredicate predicateofErrorLocations,
			final PredicateFactory predicateFactory, final IPredicateUnifier predicateUnifier,
			final InvariantSynthesisSettings invariantSynthesisSettings, final CfgSmtToolkit csToolkit,
			final KindOfInvariant kindOfInvariant) {
		mServices = services;
		mLogger = services.getLoggingService().getLogger(Activator.PLUGIN_ID);
		mCsToolKit = csToolkit;
		mKindOfInvariant = kindOfInvariant;

		mPredicateFactory = predicateFactory;
		mPredicateUnifier = predicateUnifier;
		mPredicateOfInitialLocations = predicateOfInitialLocations;
		mPredicateOfErrorLocations = predicateofErrorLocations;
		if (IcfgUtils.hasUnreachableProgramPoints(icfg)) {
			throw new IllegalArgumentException("ICFGs that have unreachable program points are not supported");
		}
		mIcfg = icfg;
		mInvariantSynthesisSettings = invariantSynthesisSettings;
		mApplyLargeBlockEncoding = mInvariantSynthesisSettings.useLargeBlockEncoding();
		mPathInvariantsStatistics = new InvariantSynthesisStatisticsGenerator();
		// Initialize statistics
		mPathInvariantsStatistics.initializeStatistics();
		mRound2InvariantSynthesisStatistics = new HashMap<>();
	}

	/**
	 * Creates a default factory.
	 *
	 * @param services
	 *            Service provider to use, for example for logging and timeouts
	 * @param predicateUnifier
	 *            the predicate unifier to unify final predicates with
	 * @param csToolkit
	 *            the smt manager for constructing the default {@link IInvariantPatternProcessorFactory}
	 * @param simplicationTechnique
	 * @param xnfConversionTechnique
	 * @param synthesizeEntryPattern
	 *            true if the the pattern for the start location need to be synthesized (instead of being inferred from
	 *            the precondition)
	 * @param kindOfInvariant
	 *            the kind of invariant to be generated
	 * @param axioms
	 * @return a default invariant pattern processor factory
	 */
	private static IInvariantPatternProcessorFactory<?> createDefaultFactory(final IUltimateServiceProvider services,
			final IPredicateUnifier predicateUnifier, final CfgSmtToolkit csToolkit, final boolean useNonlinerConstraints,
			final boolean useVarsFromUnsatCore, final SolverSettings solverSettings,
			final SimplificationTechnique simplicationTechnique, final XnfConversionTechnique xnfConversionTechnique,
			final ILinearInequalityInvariantPatternStrategy<Dnf<AbstractLinearInvariantPattern>> strategy,
			final Map<IcfgLocation, IPredicate> loc2underApprox,
			final Map<IcfgLocation, IPredicate> loc2overApprox, final boolean synthesizeEntryPattern,
			final KindOfInvariant kindOfInvariant) {

		return new LinearInequalityInvariantPatternProcessorFactory(services, predicateUnifier, csToolkit, strategy,
				useNonlinerConstraints, useVarsFromUnsatCore, solverSettings, simplicationTechnique, xnfConversionTechnique,
				csToolkit.getSmtSymbols(), loc2underApprox, loc2overApprox, synthesizeEntryPattern,
				kindOfInvariant);
	}

	/**
	 * For each idea on which variables and what kind of templates as well as which information to use from previous
	 * attempts, a strategy has been developed.
	 *
	 * @return a strategy on how to build templates and which variables to use
	 */
	private static ILinearInequalityInvariantPatternStrategy<Dnf<AbstractLinearInvariantPattern>> getStrategy(
			final boolean useVarsFromUnsatCore, final boolean useLiveVars, final Set<IProgramVar> allProgramVariables,
			final Map<IcfgLocation, Set<IProgramVar>> locations2LiveVariables,
			final AbstractTemplateIncreasingDimensionsStrategy dimensionsStrategy,
			final KindOfInvariant kindOfInvariant) {
		if (kindOfInvariant == KindOfInvariant.DANGER) {
			return new DangerInvariantPatternStrategy(dimensionsStrategy, MAX_ROUNDS, allProgramVariables,
					allProgramVariables, ALWAYS_STRICT_AND_NON_STRICT_COPIES, USE_STRICT_INEQUALITIES_ALTERNATINGLY);
		}
		assert kindOfInvariant == KindOfInvariant.SAFETY;
		if (useVarsFromUnsatCore) {
			if (USE_UNSAT_CORES_FOR_DYNAMIC_PATTERN_CHANGES) {
				if (USE_DYNAMIC_PATTERN_WITH_BOUNDS) {
					return new DynamicPatternSettingsStrategyWithBounds(dimensionsStrategy, MAX_ROUNDS,
							allProgramVariables, locations2LiveVariables, ALWAYS_STRICT_AND_NON_STRICT_COPIES,
							USE_STRICT_INEQUALITIES_ALTERNATINGLY);
				}
				if (USE_DYNAMIC_PATTERN_CHANGES_WITH_GLOBAL_TEMPLATE_LEVEL) {
					return new DynamicPatternSettingsStrategyWithGlobalTemplateLevel(dimensionsStrategy, MAX_ROUNDS,
							allProgramVariables, locations2LiveVariables, ALWAYS_STRICT_AND_NON_STRICT_COPIES,
							USE_STRICT_INEQUALITIES_ALTERNATINGLY);
				}
				return new DynamicPatternSettingsStrategy(dimensionsStrategy, MAX_ROUNDS, allProgramVariables,
						locations2LiveVariables, ALWAYS_STRICT_AND_NON_STRICT_COPIES,
						USE_STRICT_INEQUALITIES_ALTERNATINGLY);
			}
			return new VarsInUnsatCoreStrategy(dimensionsStrategy, MAX_ROUNDS, allProgramVariables,
					locations2LiveVariables, ALWAYS_STRICT_AND_NON_STRICT_COPIES,
					USE_STRICT_INEQUALITIES_ALTERNATINGLY);
		} else if (useLiveVars) {
			return new LiveVariablesStrategy(dimensionsStrategy, MAX_ROUNDS, allProgramVariables,
					locations2LiveVariables, ALWAYS_STRICT_AND_NON_STRICT_COPIES,
					USE_STRICT_INEQUALITIES_ALTERNATINGLY);
		}
		return new AllProgramVariablesStrategy(dimensionsStrategy, MAX_ROUNDS, allProgramVariables, allProgramVariables,
				ALWAYS_STRICT_AND_NON_STRICT_COPIES, USE_STRICT_INEQUALITIES_ALTERNATINGLY);
	}

	/**
	 * Generates invariants for the by extracting transitions, variables and locations from the given path program
	 * (CFG), and then applying {@link generateInvariantsForTransitions} on them.
	 */
	private Map<IcfgLocation, IPredicate> generateInvariantsForPathProgram(final IIcfg<IcfgLocation> pathProgram,
			final SimplificationTechnique simplificationTechnique, final XnfConversionTechnique xnfConversionTechnique,
			final CfgSmtToolkit csToolkit, final InvariantSynthesisSettings invSynthSettings) {

		final IcfgLocation startLocation = new ArrayList<>(pathProgram.getInitialNodes()).get(0);
		final Set<IcfgLocation> errorLocations = IcfgUtils.getErrorLocations(pathProgram);
		final List<IcfgLocation> locationsAsList = new ArrayList<>();
		final List<IcfgInternalTransition> transitionsAsList = new ArrayList<>();
		final Set<IProgramVar> allProgramVars = new HashSet<>();
		// Get locations, transitions and program variables from the path program
		extractLocationsTransitionsAndVariablesFromPathProgram(pathProgram, locationsAsList, transitionsAsList,
				allProgramVars);
		mLogger.info("Built projected CFG, " + locationsAsList.size() + " states and " + transitionsAsList.size()
				+ " transitions.");
		Map<IcfgLocation, Set<IProgramVar>> pathprogramLocs2LiveVars = null;

		final boolean useLiveVariables = USE_LIVE_VARIABLES && mKindOfInvariant != KindOfInvariant.DANGER;
		if (useLiveVariables) {
			pathprogramLocs2LiveVars = generateLiveVariables(pathProgram);
			// At the initial location no variable is live
			pathprogramLocs2LiveVars.put(startLocation, new HashSet<IProgramVar>());
			if (mLogger.isDebugEnabled()) {
				mLogger.debug("Live variables computed: " + pathprogramLocs2LiveVars);
			}
		}
		Map<IcfgLocation, IPredicate> loc2underApprox = null;
		Map<IcfgLocation, IPredicate> loc2overApprox = null;

		if (invSynthSettings.useUnsatCores()) {
			// Compute under-/overapproximation only if we use unsat cores during invariant synthesis
			final NonInductiveAnnotationGenerator underApprox = new NonInductiveAnnotationGenerator(mServices,
					mPredicateUnifier.getPredicateFactory(), pathProgram, Approximation.UNDERAPPROXIMATION);
			loc2underApprox = convertHashRelation(underApprox.getResult(), csToolkit.getManagedScript());
		}
		if (invSynthSettings.useUnsatCores() || invSynthSettings.useWeakestPrecondition()) {
			final NonInductiveAnnotationGenerator overApprox = new NonInductiveAnnotationGenerator(mServices,
					mPredicateUnifier.getPredicateFactory(), pathProgram, Approximation.OVERAPPROXIMATION);
			loc2overApprox = convertHashRelation(overApprox.getResult(), csToolkit.getManagedScript());
		}
		final Map<IcfgLocation, IPredicate> pathprogramLocs2Predicates = new HashMap<>();
		if (invSynthSettings.useWeakestPrecondition()) {
			pathprogramLocs2Predicates.putAll(loc2overApprox);
		}

		if (invSynthSettings.useAbstractInterpretation()) {
			// TODO 2018-06-10 Matthias: WIP - continue AI integration here.
			final Map<IcfgLocation, IPredicate> result = generatePredicatesViaAbstractInterpretation(pathProgram);
			pathprogramLocs2Predicates.putAll(result);
		}
		AbstractTemplateIncreasingDimensionsStrategy templateDimensionStrat =
				invSynthSettings.getTemplateDimensionsStrategy();
		if (templateDimensionStrat == null) {
			templateDimensionStrat = new DefaultTemplateIncreasingDimensionsStrategy(1, 1, 1, 1);
		}

		final ILinearInequalityInvariantPatternStrategy<Dnf<AbstractLinearInvariantPattern>> strategy =
				getStrategy(invSynthSettings.useUnsatCores(), useLiveVariables, allProgramVars,
						pathprogramLocs2LiveVars, templateDimensionStrat, mKindOfInvariant);

		if (USE_UNDER_APPROX_FOR_MAX_CONJUNCTS) {
			for (final Map.Entry<IcfgLocation, IPredicate> entry : loc2underApprox.entrySet()) {
				final List<Integer> maxDisjunctsMaxConjuncts =
						getDisjunctsAndConjunctsFromTerm(entry.getValue().getFormula());
				strategy.setNumOfConjunctsForLocation(entry.getKey(), maxDisjunctsMaxConjuncts.get(1));
			}
		} else if (USE_OVER_APPROX_FOR_MIN_DISJUNCTS) {
			for (final Map.Entry<IcfgLocation, IPredicate> entry : loc2underApprox.entrySet()) {
				final List<Integer> maxDisjunctsMaxConjuncts =
						getDisjunctsAndConjunctsFromTerm(entry.getValue().getFormula());
				strategy.setNumOfDisjunctsForLocation(entry.getKey(), maxDisjunctsMaxConjuncts.get(0));
			}
		}
		final boolean synthesizeEntryPattern = mKindOfInvariant == KindOfInvariant.DANGER;
		final IInvariantPatternProcessorFactory<?> invPatternProcFactory =
				createDefaultFactory(mServices, mPredicateUnifier, csToolkit, invSynthSettings.useNonLinearConstraints(),
						invSynthSettings.useUnsatCores(), invSynthSettings.getSolverSettings(),
						simplificationTechnique, xnfConversionTechnique, strategy, loc2underApprox,
						loc2overApprox, synthesizeEntryPattern, mKindOfInvariant);

		final Map<IcfgLocation, IPredicate> invariants =
				generateInvariantsForTransitions(locationsAsList, transitionsAsList, mPredicateOfInitialLocations,
						mPredicateOfErrorLocations, startLocation, errorLocations, invPatternProcFactory,
						invSynthSettings.useUnsatCores(), allProgramVars, pathprogramLocs2LiveVars,
						convertMapToPredsToMapToUnmodTrans(pathprogramLocs2Predicates, csToolkit.getManagedScript()),
						invSynthSettings.useWeakestPrecondition() || invSynthSettings.useAbstractInterpretation());

		return invariants;
	}

	private Map<IcfgLocation, UnmodifiableTransFormula> extractAbstractInterpretationPredicates(
			final IAbstractInterpretationResult<LiveVariableState<IcfgEdge>, IcfgEdge, IcfgLocation> abstractInterpretationResult,
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

	private static Map<IcfgLocation, IPredicate> convertHashRelation(
			final HashRelation<IcfgLocation, IPredicate> loc2SetOfPreds, final ManagedScript managedScript) {

		final Map<IcfgLocation, IPredicate> loc2Predicate = new HashMap<>(loc2SetOfPreds.getDomain().size());
		for (final IcfgLocation loc : loc2SetOfPreds.getDomain()) {
			final List<IPredicate> preds = new ArrayList<>(loc2SetOfPreds.getImage(loc).size());
			preds.addAll(loc2SetOfPreds.getImage(loc));
			// Currently, we use only one predicate
			loc2Predicate.put(loc, preds.get(0));
		}
		return loc2Predicate;
	}

	/**
	 * Collects all variables from all transitions (edges) , locations (nodes), and transitions (edges) from the given
	 * CFG (pathProgram).
	 *
	 * @param pathProgram
	 *            - the CFG for which the variables, the locations and transitions are collected.
	 * @param locationsOfPP
	 *            - collected locations are stored in this list
	 * @param transitionsOfPP
	 *            - collected transitions are stored in this list
	 * @param allVariablesFromPP
	 *            - collected variables are stored in this set
	 */
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
						throw new UnsupportedOperationException(
								"interprocedural path programs are not supported (yet)");
					}
					final UnmodifiableTransFormula tf = ((IInternalAction) e).getTransformula();
					allVariablesFromPP.addAll(tf.getInVars().keySet());
					allVariablesFromPP.addAll(tf.getOutVars().keySet());
					edges.addLast(pathProgram.getCfgSmtToolkit().getIcfgEdgeFactory()
							.createInternalTransition(e.getSource(), e.getTarget(), e.getPayload(), tf));
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

	/**
	 * Compute a predicate via abstract interpretation for each location of the given path program.
	 */
	private Map<IcfgLocation, IPredicate>
			generatePredicatesViaAbstractInterpretation(final IIcfg<IcfgLocation> pathProgram) {

		// allow for 20% of the remaining time
		final IProgressAwareTimer timer = mServices.getProgressMonitorService().getChildTimer(0.2);
		// this will run abstract interpretation with the domain specified by the settings and without generating any
		// IResults
		final IAbstractInterpretationResult<?, IcfgEdge, IcfgLocation> result =
				AbstractInterpreter.runFuture(pathProgram, timer, mServices, true, mLogger);

		// you still have to convert the term to a predicate. I do not know what kind of predicates you want, but I
		// guess you can do it like this:
		final Map<IcfgLocation, IPredicate> locs2Predicates = new HashMap<>();
		final Map<IcfgLocation, Term> loc2term = result.getLoc2Term();
		for (final Entry<IcfgLocation, Term> entry : loc2term.entrySet()) {
			final IPredicate pred = mPredicateUnifier.getOrConstructPredicate(entry.getValue());
			locs2Predicates.put(entry.getKey(), pred);
		}
		return locs2Predicates;
	}

	/**
	 * Computes for each location of the given path program a set of variables which are <emph> live </emph> on that
	 * location.
	 *
	 */
	private Map<IcfgLocation, Set<IProgramVar>> generateLiveVariables(final IIcfg<IcfgLocation> pathProgram) {
		// allow for 20% of the remaining time
		final IProgressAwareTimer timer = mServices.getProgressMonitorService().getChildTimer(0.2);
		final Map<IcfgLocation, LiveVariableState<IcfgEdge>> loc2states = AbstractInterpreter
				.runFutureLiveVariableDomain(pathProgram, timer, mServices, true, mLogger).getLoc2SingleStates();
		final Map<IcfgLocation, Set<IProgramVar>> pathprogramLocs2LiveVars = new HashMap<>();

		for (final Entry<IcfgLocation, LiveVariableState<IcfgEdge>> entry : loc2states.entrySet()) {
			pathprogramLocs2LiveVars.put(entry.getKey(), entry.getValue().getLiveVariablesAsProgramVars());
		}
		return pathprogramLocs2LiveVars;
	}

	/**
	 * Attempts to generate an invariant map for a given CFG (pair of locations and transitions) using a
	 * {@link IInvariantPatternProcessor} from the given {@link IInvariantPatternProcessorFactory}.
	 *
	 * The {@link IInvariantPatternProcessor} will be used for up to {@link IInvariantPatternProcessor#getMaxRounds()}
	 * attempts to generate such an invariant map. If all attempts fail, this method returns null.
	 *
	 * @param <IPT>
	 *            Invariant Pattern Type: Type used for invariant patterns
	 * @param precondition
	 *
	 * @param postcondition
	 *
	 * @param invPatternProcFactory
	 *            the factory to produce the {@link IInvariantPatternProcessor} with
	 * @return the invariant map for the set of given locations or null if the processor failed to process its invariant
	 *         patterns up to its final run.
	 */
	private <IPT> Map<IcfgLocation, IPredicate> generateInvariantsForTransitions(
			final List<IcfgLocation> locationsAsList, final List<IcfgInternalTransition> transitions,
			final IPredicate precondition, final IPredicate postcondition, final IcfgLocation startLocation,
			final Set<IcfgLocation> errorLocations, final IInvariantPatternProcessorFactory<IPT> invPatternProcFactory,
			final boolean useUnsatCore, final Set<IProgramVar> allProgramVars,
			final Map<IcfgLocation, Set<IProgramVar>> locs2LiveVariables,
			final Map<IcfgLocation, UnmodifiableTransFormula> pathprogramLocs2Predicates, final boolean usePredicates) {
		final IInvariantPatternProcessor<IPT> processor = invPatternProcFactory.produce(locationsAsList, transitions,
				precondition, postcondition, startLocation, errorLocations);
		mLogger.info("(Path)program has " + locationsAsList.size() + " locations");
		// Set statistics data
		mPathInvariantsStatistics.setNumOfVars(allProgramVars.size());

		final Map<IcfgLocation, IPT> locs2Patterns = new HashMap<>(locationsAsList.size());
		final Map<IcfgLocation, Set<IProgramVar>> locs2PatternVariables = new HashMap<>(locationsAsList.size());

		final Map<TermVariable, IProgramVar> smtVars2ProgramVars = new HashMap<>();
		if (useUnsatCore) {
			// Compute map smt-variables to program variables
			for (final IcfgInternalTransition t : transitions) {
				// Add value-key-pairs from transitions invars to smtVars2ProgramVars
				for (final Map.Entry<IProgramVar, TermVariable> entry : t.getTransformula().getInVars().entrySet()) {
					smtVars2ProgramVars.put(entry.getValue(), entry.getKey());
				}
				// Add value-key-pairs from transitions outvars to smtVars2ProgramVars
				for (final Map.Entry<IProgramVar, TermVariable> entry : t.getTransformula().getOutVars().entrySet()) {
					smtVars2ProgramVars.put(entry.getValue(), entry.getKey());
				}
			}
		}
		Set<IProgramVar> varsFromUnsatCore = new HashSet<>();
		if (useUnsatCore && INIT_USE_EMPTY_PATTERNS) {
			// Execute pre-round with empty patterns for intermediate locations, so we can use the variables from the
			// unsat core
			final Map<IcfgLocation, IPredicate> resultFromPreRound =
					executePreRoundWithEmptyPatterns(processor, 0, varsFromUnsatCore, locs2Patterns,
							locs2PatternVariables, smtVars2ProgramVars, startLocation, errorLocations, locationsAsList,
							transitions, allProgramVars, pathprogramLocs2Predicates, usePredicates);
			if (resultFromPreRound != null) {
				return resultFromPreRound;
			}
		}
		for (int round = 1; round < processor.getMaxRounds(); round++) {

			// Die if we run into timeouts or are otherwise requested to cancel.
			if (!mServices.getProgressMonitorService().continueProcessing()) {
				throw new ToolchainCanceledException(CFGInvariantsGenerator.class);
			}

			// Start round
			processor.startRound(round);
			mLogger.info("Round " + round + " started");

			// Build pattern map
			locs2Patterns.clear();
			locs2PatternVariables.clear();
			for (final IcfgLocation location : locationsAsList) {
				if (useUnsatCore && USE_VARS_FROM_UNSAT_CORE_FOR_EACH_LOC && round > 0) {
					locs2Patterns.put(location,
							processor.getInvariantPatternForLocation(location, round, varsFromUnsatCore));
				} else {
					locs2Patterns.put(location, processor.getInvariantPatternForLocation(location, round));
				}
				locs2PatternVariables.put(location, processor.getVariablesForInvariantPattern(location, round));
			}
			// Add under-approximation predicates (Weakest Precondition) to invariant templates
			if (usePredicates && pathprogramLocs2Predicates != null) {
				addWP_PredicatesToInvariantPatterns(processor, locs2Patterns, locs2PatternVariables,
						pathprogramLocs2Predicates);
			}
			mLogger.info("Built pattern map.");

			// Build transition predicates
			final Collection<SuccessorConstraintIngredients<IPT>> successorConstraintIngredients =
					new ArrayList<>(locationsAsList.size());
			int sumOfTemplateConjuncts = 0;
			int minimalTemplateSizeOfThisRound = Integer.MAX_VALUE;
			int maximalTemplateSizeOfThisRound = 0;
			for (final IcfgLocation location : locationsAsList) {
				final IPT invStart = locs2Patterns.get(location);
				final Set<IProgramVar> startPatternVariables = locs2PatternVariables.get(location);
				final SuccessorConstraintIngredients<IPT> successorConstraintIngredient =
						new SuccessorConstraintIngredients<>(location, startPatternVariables, invStart);

				for (final IcfgEdge transition : location.getOutgoingEdges()) {
					final IPT invEnd = locs2Patterns.get(transition.getTarget());
					final Set<IProgramVar> targetPatternVariables = locs2PatternVariables.get(transition.getTarget());
					if (mKindOfInvariant == KindOfInvariant.DANGER) {
						final IPT transitionPattern = processor.getPatternForTransition(transition, round);
						successorConstraintIngredient.addTransition(transition, invEnd, targetPatternVariables,
								transitionPattern);
					} else {
						successorConstraintIngredient.addTransition(transition, invEnd, targetPatternVariables);
					}

					// Compute the benchmarks
					@SuppressWarnings("unchecked")
					final int sizeOfTemplate2 = ((LinearInequalityInvariantPatternProcessor) processor)
							.getTotalNumberOfConjunctsInPattern((Dnf<AbstractLinearInvariantPattern>) invEnd);
					// Compute the total size of all non-trivial templates
					sumOfTemplateConjuncts = sumOfTemplateConjuncts + sizeOfTemplate2;
					if (!errorLocations.contains(transition.getTarget())) {
						if (sizeOfTemplate2 < minimalTemplateSizeOfThisRound) {
							minimalTemplateSizeOfThisRound = sizeOfTemplate2;
						}
						if (sizeOfTemplate2 > maximalTemplateSizeOfThisRound) {
							maximalTemplateSizeOfThisRound = sizeOfTemplate2;
						}
					}
				}

				successorConstraintIngredients.add(successorConstraintIngredient);
			}

			// Set statistics before check sat
			prepareAndSetPathInvariantsStatisticsBeforeCheckSat(locationsAsList, startLocation, errorLocations,
					allProgramVars, locs2LiveVariables, sumOfTemplateConjuncts, minimalTemplateSizeOfThisRound,
					maximalTemplateSizeOfThisRound, round);

			// Attempt to find a valid configuration
			final LBool constraintsResult = processor.checkForValidConfiguration(successorConstraintIngredients, round);

			Set<IcfgLocation> locsInUnsatCore = null;
			varsFromUnsatCore = null;

			if (constraintsResult == LBool.UNSAT) {
				if (useUnsatCore) {
					// Set benchmarks
					locsInUnsatCore = ((LinearInequalityInvariantPatternProcessor) processor).getLocationsInUnsatCore();
					// If no configuration could have been found, the constraints may be unsatisfiable
					final Collection<TermVariable> smtVarsFromUnsatCore =
							((LinearInequalityInvariantPatternProcessor) processor).getVarsFromUnsatCore();
					if (smtVarsFromUnsatCore != null) {
						mLogger.info(smtVarsFromUnsatCore.size() + " out of " + smtVars2ProgramVars.size()
								+ " SMT variables in unsat core");
						// The result in pattern processor was 'unsat'
						varsFromUnsatCore = new HashSet<>(smtVarsFromUnsatCore.size());
						for (final TermVariable smtVar : smtVarsFromUnsatCore) {
							if (smtVars2ProgramVars.get(smtVar) != null) {
								varsFromUnsatCore.add(smtVars2ProgramVars.get(smtVar));
							}
						}
						if (mLogger.isInfoEnabled()) {
							mLogger.info("Vars in unsat core: " + varsFromUnsatCore);
						}
						mLogger.info(varsFromUnsatCore.size() + " out of "
								+ (new HashSet<>(smtVars2ProgramVars.values())).size()
								+ " program variables in unsat core");
						if (mLogger.isInfoEnabled()) {
							mLogger.info("Locations in unsat core: " + locsInUnsatCore);
						}

						mLogger.info(locsInUnsatCore.size() + " out of " + locationsAsList.size()
								+ " locations in unsat core");
					}
				} else {
					// The result in pattern processor was 'unknown', so reset varsFromUnsatCore to null
					varsFromUnsatCore = null;
				}

			}
			// Set statistics after check sat
			final Map<LinearInequalityPatternProcessorStatistics, Object> stats =
					((LinearInequalityInvariantPatternProcessor) processor).getStatistics();
			prepareAndSetPathInvariantsStatisticsAfterCheckSat(locationsAsList, locsInUnsatCore, startLocation,
					errorLocations, allProgramVars, varsFromUnsatCore, round, constraintsResult.toString(), stats);

			if (TEMPLATE_STATISTICS_MODE) {
				final StatisticsData stat = new StatisticsData();
				stat.aggregateBenchmarkData(mRound2InvariantSynthesisStatistics.get(round));
				final IResult benchmarkResult =
						new StatisticsResult<>(Activator.PLUGIN_ID, "InvariantSynthesisStatistics", stat);
				mServices.getResultService().reportResult(Activator.PLUGIN_ID, benchmarkResult);
			}

			if (constraintsResult == LBool.SAT) {
				mLogger.info("Found valid " + "configuration in round " + round + ".");

				final Map<IcfgLocation, IPredicate> result = new HashMap<>(locationsAsList.size());
				// Extract the values for all pattern coefficients
				processor.extractValuesForPatternCoefficients();
				// Apply configuration for each pair (location, pattern) in order to obtain a predicate for each
				// location.
				for (final IcfgLocation location : locationsAsList) {
					result.put(location, processor.applyConfiguration(locs2Patterns.get(location)));
				}
				return result;
			} else if (constraintsResult == LBool.UNKNOWN) {
				mLogger.info("Got \"UNKNOWN\" in round " + round + ", giving up the invariant search.");
				break;
			}
			if (round == processor.getMaxRounds() - 1) {
				mLogger.info("Maximal number of rounds (round = " + processor.getMaxRounds()
						+ ") reached, giving up the invariant search.");
			}
		}

		return null;
	}

	public static Map<IcfgLocation, UnmodifiableTransFormula> convertMapToPredsToMapToUnmodTrans(
			final Map<IcfgLocation, IPredicate> locs2Preds, final ManagedScript managedScript) {
		if (locs2Preds == null) {
			return null;
		} else {
			final Map<IcfgLocation, UnmodifiableTransFormula> result =
					locs2Preds.keySet().stream().collect(Collectors.toMap(loc -> loc, loc -> TransFormulaBuilder
							.constructTransFormulaFromPredicate(locs2Preds.get(loc), managedScript)));
			return result;
		}
	}

	public Map<Integer, InvariantSynthesisStatisticsGenerator> getRound2PathInvariantsStatistics() {
		return mRound2InvariantSynthesisStatistics;
	}

	public final InvariantSynthesisStatisticsGenerator getInvariantSynthesisStatistics() {
		return mPathInvariantsStatistics;
	}

	private void prepareAndSetPathInvariantsStatisticsBeforeCheckSat(final List<IcfgLocation> locationsAsList,
			final IcfgLocation startLoc, final Set<IcfgLocation> errorLocs, final Set<IProgramVar> allProgramVars,
			final Map<IcfgLocation, Set<IProgramVar>> locs2LiveVariables,
			final int numOfTemplateInequalitiesForThisRound, final int minimalTemplateSizeOfThisRound,
			final int maximalTemplateSizeOfThisRound, final int round) {
		final int sumOfVarsPerLoc = allProgramVars.size() * (locationsAsList.size() - 2);
		int numOfNonLiveVariables = 0;
		for (final IcfgLocation loc : locationsAsList) {
			if (loc != startLoc && !errorLocs.contains(loc)) {
				if (locs2LiveVariables != null) {
					if (locs2LiveVariables.containsKey(loc)) {
						numOfNonLiveVariables += allProgramVars.size() - locs2LiveVariables.get(loc).size();
					}
				}
			}
		}
		mPathInvariantsStatistics.addStatisticsDataBeforeCheckSat(numOfTemplateInequalitiesForThisRound,
				maximalTemplateSizeOfThisRound, minimalTemplateSizeOfThisRound, sumOfVarsPerLoc, numOfNonLiveVariables,
				round);
		final InvariantSynthesisStatisticsGenerator pathInvariantsStatisticsForThisRound =
				new InvariantSynthesisStatisticsGenerator();
		pathInvariantsStatisticsForThisRound.initializeStatistics();
		final int numLocsBeforeLbe = (int) mPathInvariantsStatistics.getValue("ProgramLocs");
		final int numLocsAfterLbe = (int) mPathInvariantsStatistics.getValue("ProgramLocsLbe");
		pathInvariantsStatisticsForThisRound.setNumOfPathProgramLocations(numLocsBeforeLbe, numLocsAfterLbe);
		pathInvariantsStatisticsForThisRound.setNumOfVars(allProgramVars.size());
		pathInvariantsStatisticsForThisRound.addStatisticsDataBeforeCheckSat(numOfTemplateInequalitiesForThisRound,
				maximalTemplateSizeOfThisRound, minimalTemplateSizeOfThisRound, sumOfVarsPerLoc, numOfNonLiveVariables,
				round);
		mRound2InvariantSynthesisStatistics.put(round, pathInvariantsStatisticsForThisRound);
	}

	private void prepareAndSetPathInvariantsStatisticsAfterCheckSat(final List<IcfgLocation> locationsAsList,
			final Set<IcfgLocation> locationsInUnsatCore, final IcfgLocation startLoc,
			final Set<IcfgLocation> errorLocs, final Set<IProgramVar> allProgramVars,
			final Set<IProgramVar> varsFromUnsatCore, final int round, final String constraintsResult,
			final Map<LinearInequalityPatternProcessorStatistics, Object> linearInequalityStatistics) {
		int numOfNonUnsatCoreVars = 0;
		int numOfNonUnsatCoreLocs = 0;
		if (locationsInUnsatCore != null && !locationsInUnsatCore.isEmpty()) {
			numOfNonUnsatCoreLocs = locationsAsList.size() - locationsInUnsatCore.size();
		}
		for (final IcfgLocation loc : locationsAsList) {
			if (loc != startLoc && !errorLocs.contains(loc)) {
				if (varsFromUnsatCore != null) {
					numOfNonUnsatCoreVars += allProgramVars.size() - varsFromUnsatCore.size();
				}
			}
		}
		// Add statistics data to global path invariants statistics
		mPathInvariantsStatistics.addStatisticsDataAfterCheckSat(numOfNonUnsatCoreLocs, numOfNonUnsatCoreVars,
				constraintsResult, linearInequalityStatistics);
		// Add statistics data to path invariants statistics for the current round
		mRound2InvariantSynthesisStatistics.get(round).addStatisticsDataAfterCheckSat(numOfNonUnsatCoreLocs,
				numOfNonUnsatCoreVars, constraintsResult, linearInequalityStatistics);
	}

	private <IPT> void addWP_PredicatesToInvariantPatterns(final IInvariantPatternProcessor<IPT> processor,
			final Map<IcfgLocation, IPT> patterns, final Map<IcfgLocation, Set<IProgramVar>> locs2PatternVariables,
			final Map<IcfgLocation, UnmodifiableTransFormula> pathprogramLocs2WP) {
		mLogger.info("Add weakest precondition to invariant patterns.");
		for (final Map.Entry<IcfgLocation, UnmodifiableTransFormula> entry : pathprogramLocs2WP.entrySet()) {
			if (mLogger.isDebugEnabled()) {
				mLogger.debug("Loc: " + entry.getKey() + " WP: " + entry.getValue());
			}
			final IPT newPattern =
					processor.addTransFormulaToEachConjunctInPattern(patterns.get(entry.getKey()), entry.getValue());
			patterns.put(entry.getKey(), newPattern);
			final Set<IProgramVar> varsInWP = new HashSet<>(entry.getValue().getInVars().keySet());
			varsInWP.addAll(entry.getValue().getOutVars().keySet());
			// Add variables that are already assoc. with this location.
			varsInWP.addAll(locs2PatternVariables.get(entry.getKey()));
			locs2PatternVariables.put(entry.getKey(), varsInWP);
		}
	}

	/**
	 * Check if you can find an invariant with empty patterns for intermediate locations.
	 *
	 * @return
	 */
	private <IPT> Map<IcfgLocation, IPredicate> executePreRoundWithEmptyPatterns(
			final IInvariantPatternProcessor<IPT> processor, int round, Set<IProgramVar> varsFromUnsatCore,
			final Map<IcfgLocation, IPT> locs2Patterns, final Map<IcfgLocation, Set<IProgramVar>> locs2PatternVariables,
			final Map<TermVariable, IProgramVar> smtVars2ProgramVars, final IcfgLocation startLocation,
			final Set<IcfgLocation> errorLocations, final List<IcfgLocation> locationsAsList,
			final List<IcfgInternalTransition> transitions, final Set<IProgramVar> allProgramVars,
			final Map<IcfgLocation, UnmodifiableTransFormula> pathprogramLocs2Predicates, final boolean usePredicates) {
		// Start round 0 (because it's the round with empty pattern for each location)
		round = 0;
		processor.startRound(round);
		mLogger.info("Pre-round with empty patterns for intermediate locations started...");

		// Build pattern map
		locs2Patterns.clear();
		locs2PatternVariables.clear();
		for (final IcfgLocation location : locationsAsList) {
			final IPT invPattern;
			if (location.equals(startLocation)) {
				invPattern = processor.getEntryInvariantPattern();
			} else if (errorLocations.contains(location)) {
				invPattern = processor.getExitInvariantPattern();
			} else {
				// Use for intermediate locations an empty pattern
				invPattern = processor.getEmptyInvariantPattern();
			}
			locs2Patterns.put(location, invPattern);
			locs2PatternVariables.put(location, Collections.emptySet());
		}
		mLogger.info("Built (empty) pattern map");
		// add the weakest precondition of the last transition to each pattern
		if (usePredicates && pathprogramLocs2Predicates != null) {
			addWP_PredicatesToInvariantPatterns(processor, locs2Patterns, locs2PatternVariables,
					pathprogramLocs2Predicates);
		}

		// Build transition predicates
		final Collection<SuccessorConstraintIngredients<IPT>> successorConstraintIngredients =
				new ArrayList<>(locationsAsList.size());
		for (final IcfgLocation location : locationsAsList) {
			final IPT invStart = locs2Patterns.get(location);
			final Set<IProgramVar> startPatternVariables = locs2PatternVariables.get(location);
			final SuccessorConstraintIngredients<IPT> successorConstraintIngredient =
					new SuccessorConstraintIngredients<>(location, startPatternVariables, invStart);

			for (final IcfgEdge transition : location.getOutgoingEdges()) {
				final IPT invEnd = locs2Patterns.get(transition.getTarget());
				final Set<IProgramVar> targetPatternVariables = locs2PatternVariables.get(transition.getTarget());
				successorConstraintIngredient.addTransition(transition, invEnd, targetPatternVariables);
			}

			successorConstraintIngredients.add(successorConstraintIngredient);
		}

		// Attempt to find a valid configuration
		final LBool constraintsResult = processor.checkForValidConfiguration(successorConstraintIngredients, round);
		if (constraintsResult == LBool.SAT) {
			mLogger.info("Found valid configuration in pre-round.");
			final Map<IcfgLocation, IPredicate> result = new HashMap<>(locationsAsList.size());
			// Extract the values for all pattern coefficients
			processor.extractValuesForPatternCoefficients();
			// Apply configuration for each pair (location, pattern) in order to obtain a predicate for each location.
			for (final IcfgLocation location : locationsAsList) {
				final IPredicate p = processor.applyConfiguration(locs2Patterns.get(location));
				result.put(location, p);
			}
			return result;
		}
		// If no configuration could have been found, the constraints may be unsatisfiable
		final Collection<TermVariable> smtVarsFromUnsatCore =
				((LinearInequalityInvariantPatternProcessor) processor).getVarsFromUnsatCore();
		// Set benchmarks
		final Set<IcfgLocation> locsInUnsatCore =
				((LinearInequalityInvariantPatternProcessor) processor).getLocationsInUnsatCore();

		if (smtVarsFromUnsatCore != null) {
			mLogger.info(smtVarsFromUnsatCore.size() + " out of " + smtVars2ProgramVars.size()
					+ " SMT variables in unsat core");
			// The result in pattern processor was 'unsat'
			// varsFromUnsatCore = new HashSet<>(smtVarsFromUnsatCore.size());
			for (final TermVariable smtVar : smtVarsFromUnsatCore) {
				if (smtVars2ProgramVars.get(smtVar) != null) {
					varsFromUnsatCore.add(smtVars2ProgramVars.get(smtVar));
				}
			}
			if (locsInUnsatCore != null && !locsInUnsatCore.isEmpty()) {
				// mPathInvariantsStatistics.setLocationAndVariablesData(locationsAsList.size() -
				// locsInUnsatCore.size(),
				// allProgramVars.size() - varsFromUnsatCore.size());
			}
			mLogger.info(varsFromUnsatCore.size() + " out of " + (new HashSet<>(smtVars2ProgramVars.values())).size()
					+ " program variables in unsat core");
			mLogger.info(locsInUnsatCore.size() + " out of " + locationsAsList.size() + " locations in unsat core");
		} else {
			// The result in pattern processor was 'unknown', so reset varsFromUnsatCore to null
			varsFromUnsatCore = null;
		}
		mLogger.info("No valid configuration found in pre-round.");
		return null;
	}

	private int getNumOfPPLocations(final IIcfg<IcfgLocation> pathProgram) {
		int numLocs = 0;
		for (final String proc : pathProgram.getProgramPoints().keySet()) {
			numLocs += pathProgram.getProgramPoints().get(proc).keySet().size();
		}
		return numLocs;
	}

	/**
	 * Tries {@link MAX_ROUNDS} to synthesize invariants for the CFG passed in the constructor.
	 *
	 * @return - in case of success each node of the CFG (Location) is mapped to an invariant (IPredicate), otherwise
	 *         null.
	 */
	public Map<IcfgLocation, IPredicate> synthesizeInvariants() {
		final int numLocsBeforeLbe = getNumOfPPLocations(mIcfg);
		LargeBlockEncodingIcfgTransformer lbeTransformer = null;
		IIcfg<IcfgLocation> lbePathProgram;
		if (mApplyLargeBlockEncoding) {
			lbeTransformer = new LargeBlockEncodingIcfgTransformer(mServices, mPredicateFactory, mPredicateUnifier);
			lbePathProgram = lbeTransformer.transform(mIcfg);
		} else {
			lbePathProgram = mIcfg;
		}
		// BranchUnfoldIcfgTransformer buTransformer = null;
		// if (true) {
		// buTransformer = new BranchUnfoldIcfgTransformer(mServices, mPredicateFactory, mPredicateUnifier);
		// lbePathProgram = buTransformer.transform(lbePathProgram);
		// }

		final int numLocsAfterLbe = getNumOfPPLocations(lbePathProgram);
		mPathInvariantsStatistics.setNumOfPathProgramLocations(numLocsBeforeLbe, numLocsAfterLbe);

		Map<IcfgLocation, IPredicate> invariants = generateInvariantsForPathProgram(lbePathProgram,
				SimplificationTechnique.SIMPLIFY_DDA, XnfConversionTechnique.BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION,
				mCsToolKit, mInvariantSynthesisSettings);

		if (invariants != null) {
			// invariants = buTransformer.transform(invariants);
			if (mApplyLargeBlockEncoding) {
				invariants = lbeTransformer.transform(invariants);
			}
			return invariants;
		}
		return null;
	}
}
