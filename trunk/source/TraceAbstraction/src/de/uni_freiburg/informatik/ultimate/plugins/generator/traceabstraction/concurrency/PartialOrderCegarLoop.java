/*
 * Copyright (C) 2020 Marcel Ebbinghaus
 * Copyright (C) 2020-2022 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2020-2022 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.concurrency;

import java.io.File;
import java.io.FileNotFoundException;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Scanner;
import java.util.Set;
import java.util.function.Predicate;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.IRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.DeterminizeNwa;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.InformationStorage;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.PowersetDeterminizer;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.TotalizeNwa;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.AcceptingRunSearchVisitor;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.CoveringOptimizationVisitor;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.CoveringOptimizationVisitor.CoveringMode;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.DeadEndOptimizingSearchVisitor;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.DefaultIndependenceCache;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.IDfsVisitor;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.IIndependenceRelation;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.SleepSetCoveringRelation;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.SleepSetVisitorSearch;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.WrapperVisitor;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.multireduction.CoinFlipBudget;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.multireduction.OptimisticBudget;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.multireduction.SleepMapReduction.IBudgetFunction;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IDeterminizeStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IIntersectionStateFactory;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IcfgUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdgeIterator;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.debugidentifiers.DebugIdentifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.ChainingHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.HoareTripleCheckerUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.HoareTripleCheckerUtils.HoareTripleChecks;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.IHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.MonolithicHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.TransferrerWithVariableCache;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.interpolant.QualifiedTracePredicates;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.interpolant.TracePredicates;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IMLPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.ISLPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.MLPredicateWithConjuncts;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateUnifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.UnionPredicateCoverageChecker;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.tracehandling.IRefinementEngineResult;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.tracehandling.IRefinementEngineResult.BasicRefinementEngineResult;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.CommuhashNormalForm;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.IteRemover;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.solverbuilder.SolverBuilder;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.solverbuilder.SolverBuilder.ExternalSolver;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.solverbuilder.SolverBuilder.SolverMode;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.solverbuilder.SolverBuilder.SolverSettings;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.ILooperCheck;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.BetterLockstepOrder;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.LoopLockstepOrder.PredicateWithLastThread;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.PartialOrderMode;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.PartialOrderReductionFacade;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.SleepSetStateFactoryForRefinement.SleepPredicate;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.independence.IndependenceBuilder;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.independence.IndependenceSettings;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.independence.IndependenceSettings.AbstractionType;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.independence.IndependenceSettings.IndependenceType;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.independence.LooperIndependenceRelation;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.independence.abstraction.ICopyActionFactory;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.independence.abstraction.IRefinableAbstraction;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.independence.abstraction.RefinableCachedAbstraction;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.independence.abstraction.SpecificVariableAbstraction;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.independence.abstraction.SpecificVariableAbstraction.TransFormulaAuxVarEliminator;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.independence.abstraction.VariableAbstraction;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.singletracecheck.InterpolationTechnique;
import de.uni_freiburg.informatik.ultimate.logic.FormulaUnLet;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.BasicCegarLoop;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.CegarLoopStatisticsDefinitions;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.PredicateFactoryRefinement;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interpolantautomata.transitionappender.AbstractInterpolantAutomaton;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interpolantautomata.transitionappender.DeterministicInterpolantAutomaton;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences.InterpolantAutomatonEnhancement;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.CoinflipMode;
import de.uni_freiburg.informatik.ultimate.smtsolver.external.TermParseUtils;
import de.uni_freiburg.informatik.ultimate.util.Lazy;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ImmutableList;

/**
 * A CEGAR loop for concurrent programs, based on finite automata, which uses Partial Order Reduction (POR) in every
 * iteration to improve efficiency.
 *
 * @author Marcel Ebbinghaus
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 *
 * @param <L>
 *            The type of statements in the program.
 */
public class PartialOrderCegarLoop<L extends IIcfgTransition<?>>
		extends BasicCegarLoop<L, INwaOutgoingLetterAndTransitionProvider<L, IPredicate>> {

	public static boolean READ_PROOF = false;

	private final PartialOrderMode mPartialOrderMode;
	private final IIntersectionStateFactory<IPredicate> mFactory = new InformationStorageFactory();
	private final PartialOrderReductionFacade<L> mPOR;
	private final List<IRefinableIndependenceContainer<L>> mIndependenceContainers;
	private ManagedScript mIndependenceScript;

	private final List<AbstractInterpolantAutomaton<L>> mAbstractItpAutomata = new LinkedList<>();

	public PartialOrderCegarLoop(final DebugIdentifier name,
			final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> initialAbstraction,
			final IIcfg<IcfgLocation> rootNode, final CfgSmtToolkit csToolkit, final PredicateFactory predicateFactory,
			final TAPreferences taPrefs, final Set<IcfgLocation> errorLocs, final InterpolationTechnique interpolation,
			final IUltimateServiceProvider services, final ICopyActionFactory<L> copyFactory,
			final Class<L> transitionClazz, final PredicateFactoryRefinement stateFactoryForRefinement) {
		super(name, initialAbstraction, rootNode, csToolkit, predicateFactory, taPrefs, errorLocs, interpolation, false,
				Collections.emptySet(), services, transitionClazz, stateFactoryForRefinement);

		assert !mPref.applyOneShotPOR() : "Turn off one-shot partial order reduction when using this CEGAR loop.";
		if (mPref.applyOneShotLbe()) {
			throw new UnsupportedOperationException(
					"Soundness is currently not guaranteed for this CEGAR loop if one-shot LBE is turned on.");
		}

		mPartialOrderMode = mPref.getPartialOrderMode();

		// Setup management of abstraction levels and corresponding independence relations.
		final int numIndependenceRelations = mPref.getNumberOfIndependenceRelations();
		mIndependenceContainers = new ArrayList<>(numIndependenceRelations);
		mLogger.info("Running %s with %d independence relations.", PartialOrderCegarLoop.class.getSimpleName(),
				numIndependenceRelations);
		if (numIndependenceRelations > 1) {
			mLogger.warn("Attention: Unsuitable combinations of independence relations may be unsound!");
			mLogger.warn("Only combine independence relations if you are sure the combination is sound.");
		}
		for (int i = 0; i < numIndependenceRelations; ++i) {
			final IRefinableIndependenceContainer<L> container = constructIndependenceContainer(i, copyFactory);
			container.initialize();
			mIndependenceContainers.add(container);
		}

		final List<IIndependenceRelation<IPredicate, L>> relations = mIndependenceContainers.stream()
				.map(IRefinableIndependenceContainer::getOrConstructIndependence).collect(Collectors.toList());
		mPOR = new PartialOrderReductionFacade<>(services, predicateFactory, rootNode, errorLocs,
				mPref.getPartialOrderMode(), mPref.getDfsOrderType(), mPref.getDfsOrderSeed(), relations);

		if (READ_PROOF) {
			mLogger.warn("=== Iteration -1 : Refine with given proof ===");
			final String filename = ILocation.getAnnotation(rootNode).getFileName() + ".proof.smt2";
			final String path = Paths.get(filename).toAbsolutePath().toString();
			final List<IPredicate> predicates = new ArrayList<>();
			try {
				final File myObj = new File(path);
				final Scanner myReader = new Scanner(myObj);
				while (myReader.hasNextLine()) {
					final String data = myReader.nextLine();
					if (data.isBlank() || data.stripLeading().startsWith("#")) {
						continue;
					}
					final Term term = parseWithVariables(data);
					final IPredicate pred = mPredicateFactory.newPredicate(term);
					predicates.add(pred);
				}
				myReader.close();
			} catch (final FileNotFoundException e) {
				throw new IllegalStateException("could not find proof: " + path);
			}

			final IPredicateUnifier unifier = new PredicateUnifier(mLogger, mServices, mCsToolkit.getManagedScript(),
					mPredicateFactory, mCsToolkit.getSymbolTable(), mSimplificationTechnique, mXnfConversionTechnique,
					predicates.toArray(IPredicate[]::new));

			final NestedWordAutomaton<L, IPredicate> nwa = new NestedWordAutomaton<>(
					new AutomataLibraryServices(services), mAbstraction.getVpAlphabet(), mStateFactoryForRefinement);
			final IPredicate truePred = unifier.getTruePredicate();
			nwa.addState(true, false, truePred);
			final IPredicate falsePred = unifier.getFalsePredicate();
			nwa.addState(false, true, falsePred);
			for (final IPredicate pred : predicates) {
				nwa.addState(false, false, pred);
			}

			mRefinementResult = new BasicRefinementEngineResult<>(LBool.UNSAT, nwa, null, false,
					List.of(new QualifiedTracePredicates(new TracePredicates(truePred, falsePred, predicates),
							getClass(), false)),
					new Lazy<>(() -> new MonolithicHoareTripleChecker(mCsToolkit)), new Lazy<>(() -> unifier));
			mInterpolAutomaton = mRefinementResult.getInfeasibilityProof();

			try {
				refineAbstraction();
			} catch (final AutomataLibraryException e) {
				throw new IllegalStateException(e);
			}
		}
	}

	private Term parseWithVariables(final String syntax) {
		final String declarations = mIcfg.getCfgSmtToolkit().getSymbolTable().getGlobals().stream()
				.map(pv -> "(" + pv.getTermVariable().getName() + " " + pv.getSort() + ")")
				.collect(Collectors.joining(" "));
		final String fullSyntax = "(forall (" + declarations + ") " + syntax + ")";
		final var script = mCsToolkit.getManagedScript().getScript();
		final QuantifiedFormula quant = (QuantifiedFormula) TermParseUtils.parseTerm(script, fullSyntax);
		final Term noLet = new FormulaUnLet().transform(quant.getSubformula());
		final Term noIte = new IteRemover(mCsToolkit.getManagedScript()).transform(noLet);
		return new CommuhashNormalForm(mServices, script).transform(noIte);
	}

	@Override
	protected boolean refineAbstraction() throws AutomataLibraryException {
		// Compute the enhanced interpolant automaton
		final IPredicateUnifier predicateUnifier = mRefinementResult.getPredicateUnifier();
		final IHoareTripleChecker htc = getHoareTripleChecker();
		final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> ia = enhanceInterpolantAutomaton(
				mPref.interpolantAutomatonEnhancement(), predicateUnifier, htc, mInterpolAutomaton);
		if (ia instanceof AbstractInterpolantAutomaton<?>) {
			final AbstractInterpolantAutomaton<L> aia = (AbstractInterpolantAutomaton<L>) ia;
			aia.switchToReadonlyMode();
			mAbstractItpAutomata.add(aia);
		} else {
			mCegarLoopBenchmark.reportInterpolantAutomatonStates(ia.size());
		}

		// Automaton must be total and deterministic
		final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> determinized;
		switch (mPref.interpolantAutomatonEnhancement()) {
		case PREDICATE_ABSTRACTION:
		case PREDICATE_ABSTRACTION_CANNIBALIZE:
		case PREDICATE_ABSTRACTION_CONSERVATIVE:
			// already total and deterministic
			assert ia instanceof DeterministicInterpolantAutomaton<?>;
			determinized = ia;
			break;
		case NONE:
			// make automaton total
			final IPredicate initialSink = DataStructureUtils.getOneAndOnly(ia.getInitialStates(), "initial state");
			assert initialSink == predicateUnifier.getTruePredicate() : "initial state should be TRUE";
			final TotalizeNwa<L, IPredicate> totalInterpol = new TotalizeNwa<>(ia, initialSink, false);

			// determinize total automaton
			final var det = new PowersetDeterminizer<>(totalInterpol, false, new DeterminizationFactory());
			determinized = new DeterminizeNwa<>(new AutomataLibraryServices(mServices), totalInterpol, det,
					mStateFactoryForRefinement, null, false);
			break;
		default:
			throw new UnsupportedOperationException("PartialOrderCegarLoop currently does not support enhancement "
					+ mPref.interpolantAutomatonEnhancement());
		}

		// Actual refinement step
		mAbstraction = new InformationStorage<>(mAbstraction, determinized, mFactory, false);

		// update independence relations (in case of abstract independence)
		for (int i = 0; i < mIndependenceContainers.size(); ++i) {
			final var container = mIndependenceContainers.get(i);
			container.refine(mRefinementResult);
			mPOR.replaceIndependence(i, container.getOrConstructIndependence());
		}

		// TODO (Dominik 2020-12-17) Really implement this acceptance check (see BasicCegarLoop::refineAbstraction)
		return true;
	}

	@Override
	protected boolean isAbstractionEmpty() throws AutomataOperationCanceledException {
		switchToOnDemandConstructionMode();

		mCegarLoopBenchmark.start(CegarLoopStatisticsDefinitions.EmptinessCheckTime);
		try {
			IBudgetFunction<L, IPredicate> budget = new OptimisticBudget<>(new AutomataLibraryServices(mServices),
					mPOR.getDfsOrder(), mPOR.getSleepMapFactory(), this::createVisitor);
			if (mPref.useCoinflip() == CoinflipMode.FALLBACK) {
				budget = new CoinFlipBudget<>(true, mPref.coinflipSeed(), mPref.getCoinflipProbability(mIteration),
						budget);
			} else if (mPref.useCoinflip() == CoinflipMode.PURE) {
				budget = new CoinFlipBudget<>(true, mPref.coinflipSeed(), mPref.getCoinflipProbability(mIteration),
						(s, l) -> 1);
			}
			mPOR.setBudget(budget);

			final IDfsVisitor<L, IPredicate> visitor = createVisitor();
			mPOR.apply(mAbstraction, visitor);
			mCounterexample = getCounterexample(visitor);
			switchToReadonlyMode();

			assert mCounterexample == null || accepts(getServices(), mAbstraction, mCounterexample.getWord(),
					false) : "Counterexample is not accepted by abstraction";
			return mCounterexample == null;
		} finally {
			mCegarLoopBenchmark.stop(CegarLoopStatisticsDefinitions.EmptinessCheckTime);
		}
	}

	@Override
	public void finish() {
		for (final AbstractInterpolantAutomaton<L> ia : mAbstractItpAutomata) {
			mCegarLoopBenchmark.reportInterpolantAutomatonStates(ia.size());
		}
		mPOR.reportStatistics(Activator.PLUGIN_ID);

		if (mIndependenceScript != null) {
			// Shutdown the script
			// TODO Share independence script and independence relation (including cache) between CEGAR loop instances!
			mIndependenceScript.getScript().exit();
		}

		super.finish();
	}

	private IRun<L, IPredicate> getCounterexample(IDfsVisitor<L, IPredicate> visitor) {
		if (visitor instanceof WrapperVisitor<?, ?, ?>) {
			visitor = ((WrapperVisitor<L, IPredicate, IDfsVisitor<L, IPredicate>>) visitor).getBaseVisitor();
		}
		if (mPartialOrderMode.hasSleepSets() && !mPartialOrderMode.doesUnrolling()) {
			// TODO Refactor sleep set reductions to full DFS and always use (simpler) AcceptingRunSearchVisitor
			return ((SleepSetVisitorSearch<L, IPredicate>) visitor).constructRun();
		}
		return ((AcceptingRunSearchVisitor<L, IPredicate>) visitor).getAcceptingRun();
	}

	private IDfsVisitor<L, IPredicate> createVisitor() {
		IDfsVisitor<L, IPredicate> visitor;
		if (mPartialOrderMode.hasSleepSets() && !mPartialOrderMode.doesUnrolling()) {
			// TODO Refactor sleep set reductions to full DFS and always use (simpler) AcceptingRunSearchVisitor
			// TODO once this is done, we can also give a more precise return type and avoid casts in getCounterexample
			visitor = new SleepSetVisitorSearch<>(this::isGoalState, this::isProvenState);
		} else {
			visitor = new AcceptingRunSearchVisitor<>(this::isGoalState, this::isProvenState);
		}
		if (mPOR.getDfsOrder() instanceof BetterLockstepOrder<?, ?>) {
			visitor = ((BetterLockstepOrder<L, IPredicate>) mPOR.getDfsOrder()).wrapVisitor(visitor);
		}

		if (PartialOrderReductionFacade.ENABLE_COVERING_OPTIMIZATION) {
			visitor = new CoveringOptimizationVisitor<>(visitor, new SleepSetCoveringRelation<>(mPOR.getSleepFactory()),
					CoveringMode.PRUNE);
		}
		return new DeadEndOptimizingSearchVisitor<>(visitor, mPOR.getDeadEndStore(), true);
	}

	private IRefinableIndependenceContainer<L> constructIndependenceContainer(final int index,
			final ICopyActionFactory<L> copyFactory) {
		final IndependenceSettings settings = mPref.porIndependenceSettings(index);
		mLogger.info("Independence Relation #%d: %s", index + 1, settings);

		if (settings.getAbstractionType() == AbstractionType.LOOPER) {
			return new IndependenceContainerForLoopers<>(mServices, mCsToolkit, settings.getIndependenceType());
		}

		// Construct the script used for independence checks.
		// TODO Only construct this if an independence relation actually needs a script!
		// TODO problem: auxVar constants in abstraction can still not be created in the locked Icfg script.
		if (mIndependenceScript == null) {
			mIndependenceScript = constructIndependenceScript(settings);
		}

		// We need to transfer given transition formulas and condition predicates to the independenceScript.
		// TODO Only construct this if we actually need to transfer to a different script!
		final TransferrerWithVariableCache transferrer =
				new TransferrerWithVariableCache(mCsToolkit.getManagedScript().getScript(), mIndependenceScript);

		if (settings.getAbstractionType() == AbstractionType.NONE) {
			// Construct the independence relation (without abstraction). It is the responsibility of the independence
			// relation to transfer any terms (transition formulas and condition predicates) to the independenceScript.
			final var independence = constructIndependence(settings, mIndependenceScript, transferrer, false);
			return new StaticIndependenceContainer<>(independence);
		}

		// Construct the abstraction function.
		final var letterAbstraction = constructAbstraction(settings, copyFactory, mIndependenceScript, transferrer);
		final var cachedAbstraction = new RefinableCachedAbstraction<>(letterAbstraction);

		// Construct the independence relation (still without abstraction).
		// It is the responsibility of the abstraction function to transfer the transition formulas. But we leave it to
		// the independence relation to transfer conditions.
		final var independence = constructIndependence(settings, mIndependenceScript, transferrer, true);

		return new IndependenceContainerWithAbstraction<>(cachedAbstraction, independence);
	}

	private IIndependenceRelation<IPredicate, L> constructIndependence(final IndependenceSettings settings,
			final ManagedScript independenceScript, final TransferrerWithVariableCache transferrer,
			final boolean tfsAlreadyTransferred) {
		if (settings.getIndependenceType() == IndependenceType.SYNTACTIC) {
			return IndependenceBuilder.<L, IPredicate> syntactic().cached(new DefaultIndependenceCache<>())
					.threadSeparated().build();
		}

		assert settings.getIndependenceType() == IndependenceType.SEMANTIC : "unsupported independence type";
		return IndependenceBuilder
				// Semantic independence forms the base.
				// If transition formulas are already transferred to the independenceScript, we need not transfer them
				// here. Otherwise, pass on the transferrer. Conditions are handled below.
				.<L> semantic(getServices(), independenceScript, tfsAlreadyTransferred ? null : transferrer,
						settings.useConditional(), !settings.useSemiCommutativity())
				// If TFs have already been transferred and the relation is conditional, then we need to also transfer
				// the condition predicates to the independenceScript.
				.ifThen(tfsAlreadyTransferred && settings.useConditional(),
						b -> b.withTransformedPredicates(transferrer::transferPredicate))
				// Add syntactic independence check (cheaper sufficient condition).
				.withSyntacticCheck()
				// Cache independence query results.
				.cached(new DefaultIndependenceCache<>())
				// Setup condition optimization (if conditional independence is enabled).
				// =========================================================================
				// NOTE: Soundness of the condition elimination here depends on the fact that all inconsistent
				// predicates are syntactically equal to "false". Here, this is achieved by usage of
				// #withDisjunctivePredicates: The only predicates we use as conditions are the original interpolants
				// (i.e., not conjunctions of them), where we assume this constraint holds.
				.withConditionElimination(PartialOrderCegarLoop::isFalseLiteral)
				// We ignore "don't care" conditions stemming from the initial program automaton states.
				.withFilteredConditions(p -> !mPredicateFactory.isDontCare(p))
				.withDisjunctivePredicates(PartialOrderCegarLoop::getConjuncts)
				// =========================================================================
				// Never consider letters of the same thread to be independent.
				.threadSeparated()
				// Retrieve the constructed relation.
				.build();
	}

	private ManagedScript constructIndependenceScript(final IndependenceSettings settings) {
		final SolverSettings solverSettings;
		if (settings.getSolver() == ExternalSolver.SMTINTERPOL) {
			solverSettings = SolverBuilder.constructSolverSettings().setSolverMode(SolverMode.Internal_SMTInterpol)
					.setSmtInterpolTimeout(settings.getSolverTimeout())
					.setDumpSmtScriptToFile(true, ".", "commutativity", false);
		} else {
			solverSettings = SolverBuilder.constructSolverSettings().setSolverMode(SolverMode.External_DefaultMode)
					.setUseExternalSolver(settings.getSolver(), settings.getSolverTimeout())
					.setDumpSmtScriptToFile(true, ".", "commutativity", false);
		}

		return mCsToolkit.createFreshManagedScript(mServices, solverSettings, "SemanticIndependence");
	}

	private IRefinableAbstraction<NestedWordAutomaton<L, IPredicate>, ?, L> constructAbstraction(
			final IndependenceSettings settings, final ICopyActionFactory<L> copyFactory,
			final ManagedScript abstractionScript, final TransferrerWithVariableCache transferrer) {
		if (settings.getAbstractionType() == AbstractionType.NONE) {
			return null;
		}

		final Set<IProgramVar> allVariables = IcfgUtils.collectAllProgramVars(mCsToolkit);

		// We eliminate auxiliary variables.
		// This is useful both for semantic independence (ease the load on the SMT solver),
		// but even more so for syntactic independence (often allows shrinking the set of "read" variables).
		final TransFormulaAuxVarEliminator tfEliminator = (ms, fm, av) -> TransFormulaUtils
				.tryAuxVarElimination(mServices, ms, SimplificationTechnique.POLY_PAC, fm, av);

		switch (settings.getAbstractionType()) {
		case VARIABLES_GLOBAL:
			return new VariableAbstraction<>(copyFactory, abstractionScript, transferrer, tfEliminator, allVariables);
		case VARIABLES_LOCAL:
			if (mPref.interpolantAutomatonEnhancement() != InterpolantAutomatonEnhancement.NONE) {
				throw new UnsupportedOperationException(
						"specific variable abstraction is only supported with interpolant automaton enhancement NONE");
			}

			// TODO Should this be replaced with mAbstraction.getAlphabet()?
			// Note that this would require changes to ThreadBasedPersistentSets, because it also considers
			// commutativity of forkCurrent and joinCurrent transitions, which are not in the alphabet.
			final Set<L> allLetters =
					new IcfgEdgeIterator(mIcfg).asStream().map(x -> (L) x).collect(Collectors.toSet());
			return new SpecificVariableAbstraction<>(copyFactory, abstractionScript, transferrer, tfEliminator,
					allVariables, allLetters);
		default:
			throw new UnsupportedOperationException("Unknown abstraction type: " + settings.getAbstractionType());
		}
	}

	private void switchToOnDemandConstructionMode() {
		for (final AbstractInterpolantAutomaton<L> aut : mAbstractItpAutomata) {
			aut.switchToOnDemandConstructionMode();
		}
	}

	private void switchToReadonlyMode() {
		for (final AbstractInterpolantAutomaton<L> aut : mAbstractItpAutomata) {
			aut.switchToReadonlyMode();
		}
	}

	private boolean isGoalState(final IPredicate state) {
		assert state instanceof IMLPredicate || state instanceof ISLPredicate : "unexpected type of predicate: "
				+ state.getClass();

		final boolean isErrorState;
		if (state instanceof ISLPredicate) {
			isErrorState = mErrorLocs.contains(((ISLPredicate) state).getProgramPoint());
		} else {
			isErrorState = Arrays.stream(((IMLPredicate) state).getProgramPoints()).anyMatch(mErrorLocs::contains);
		}
		return isErrorState && !isProvenState(state);
	}

	private boolean isProvenState(IPredicate state) {
		final PartialOrderReductionFacade.StateSplitter<IPredicate> splitter = mPOR.getStateSplitter();
		if (splitter != null) {
			state = splitter.getOriginal(state);
		}
		return isFalseLiteral(state);
	}

	private static boolean isFalseLiteral(final IPredicate state) {
		if (state instanceof MLPredicateWithConjuncts) {
			// By the way we create conjunctions in the state factory below, any conjunction that contains the conjunct
			// "false" will contain no other conjuncts.
			final ImmutableList<IPredicate> conjuncts = ((MLPredicateWithConjuncts) state).getConjuncts();
			return conjuncts.size() == 1 && isFalseLiteral(conjuncts.getHead());
		}

		// We assume here that all inconsistent interpolant predicates are syntactically equal to "false".
		return SmtUtils.isFalseLiteral(state.getFormula());
	}

	private static boolean isTrueLiteral(final IPredicate state) {
		if (state instanceof MLPredicateWithConjuncts) {
			final ImmutableList<IPredicate> conjuncts = ((MLPredicateWithConjuncts) state).getConjuncts();
			return conjuncts.size() == 1 && isTrueLiteral(conjuncts.getHead());
		}
		return SmtUtils.isTrueLiteral(state.getFormula());
	}

	private static List<IPredicate> getConjuncts(final IPredicate conjunction) {
		if (conjunction == null) {
			return ImmutableList.empty();
		}
		if (conjunction instanceof MLPredicateWithConjuncts) {
			return ((MLPredicateWithConjuncts) conjunction).getConjuncts();
		}

		// TODO use mPOR.mStateSplitter for this
		if (conjunction instanceof PredicateWithLastThread) {
			return getConjuncts(((PredicateWithLastThread) conjunction).getUnderlying());
		}
		if (conjunction instanceof SleepPredicate<?>) {
			return getConjuncts(((SleepPredicate<?>) conjunction).getUnderlying());
		}

		return ImmutableList.singleton(conjunction);
	}

	@Override
	protected void constructErrorAutomaton() throws AutomataOperationCanceledException {
		throw new UnsupportedOperationException("Error automata not supported for " + PartialOrderCegarLoop.class);
	}

	@Override
	protected void computeIcfgHoareAnnotation() {
		throw new UnsupportedOperationException("Hoare annotation not supported for " + PartialOrderCegarLoop.class);
	}

	private final class InformationStorageFactory implements IIntersectionStateFactory<IPredicate> {
		@Override
		public IPredicate createEmptyStackState() {
			return mStateFactoryForRefinement.createEmptyStackState();
		}

		@Override
		public IPredicate intersection(final IPredicate state1, final IPredicate state2) {
			if (isFalseLiteral(state1) || isTrueLiteral(state2)) {
				// If state1 is "false", we add no other conjuncts, and do not create a new state.
				// Similarly, there is no point in adding state2 as conjunct if it is "true".
				return state1;
			}

			final IPredicate newState;
			if (isFalseLiteral(state2) || isTrueLiteral(state1)) {
				// If state2 is "false", we ignore all previous conjuncts. This allows us to optimize in #isFalseLiteral
				// As another (less important) optimization, we also ignore state1 if it is "true".
				newState = mPredicateFactory.construct(id -> new MLPredicateWithConjuncts(id,
						((IMLPredicate) state1).getProgramPoints(), ImmutableList.singleton(state2)));
			} else {
				// In the normal case, we simply add state2 as conjunct.
				newState = mPredicateFactory
						.construct(id -> new MLPredicateWithConjuncts(id, (IMLPredicate) state1, state2));
			}

			mPOR.getDeadEndStore().copyDeadEndInformation(state1, newState);
			return newState;
		}
	}

	private final class DeterminizationFactory implements IDeterminizeStateFactory<IPredicate> {
		@Override
		public IPredicate createEmptyStackState() {
			return mPredicateFactoryInterpolantAutomata.createEmptyStackState();
		}

		@Override
		public IPredicate determinize(final Map<IPredicate, Set<IPredicate>> down2up) {
			// No support for calls and returns means the map should always have a simple structure.
			assert down2up.size() == 1 && down2up.containsKey(createEmptyStackState());
			final Set<IPredicate> conjuncts = down2up.get(createEmptyStackState());

			// Interpolant automaton should not have "don't care".
			assert conjuncts.stream().noneMatch(mPredicateFactory::isDontCare);

			// Don't create unnecessary conjunctions of single predicates.
			if (conjuncts.size() == 1) {
				return DataStructureUtils.getOneAndOnly(conjuncts, "predicate");
			}

			return mPredicateFactory.and(conjuncts);
		}
	}

	/**
	 * Encapsulates management of abstraction levels and corresponding independence relations.
	 *
	 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
	 *
	 * @param <L>
	 *            The type of letters for which an independence relation is managed.
	 */
	private interface IRefinableIndependenceContainer<L extends IIcfgTransition<?>> {
		void initialize();

		void refine(IRefinementEngineResult<L, NestedWordAutomaton<L, IPredicate>> refinement);

		IIndependenceRelation<IPredicate, L> getOrConstructIndependence();
	}

	/**
	 * An {@link IRefinableIndependenceContainer} implementation for the case where we only consider concrete
	 * commutativity.
	 *
	 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
	 */
	private static class StaticIndependenceContainer<L extends IIcfgTransition<?>>
			implements IRefinableIndependenceContainer<L> {
		private final IIndependenceRelation<IPredicate, L> mIndependence;

		public StaticIndependenceContainer(final IIndependenceRelation<IPredicate, L> independence) {
			mIndependence = independence;
		}

		@Override
		public void initialize() {
			// nothing to initialize
		}

		@Override
		public void refine(final IRefinementEngineResult<L, NestedWordAutomaton<L, IPredicate>> refinement) {
			// nothing to refine
		}

		@Override
		public IIndependenceRelation<IPredicate, L> getOrConstructIndependence() {
			return mIndependence;
		}
	}

	/**
	 * An {@link IRefinableIndependenceContainer} implementation for the case where we consider abstract commutativity
	 * given by some refinable abstraction function.
	 *
	 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
	 *
	 * @param <H>
	 *            The type of abstraction levels
	 */
	private static class IndependenceContainerWithAbstraction<L extends IIcfgTransition<?>, H>
			implements IRefinableIndependenceContainer<L> {
		private final IRefinableAbstraction<NestedWordAutomaton<L, IPredicate>, H, L> mRefinableAbstraction;
		private final IIndependenceRelation<IPredicate, L> mUnderlyingIndependence;
		private H mAbstractionLevel;

		public IndependenceContainerWithAbstraction(
				final IRefinableAbstraction<NestedWordAutomaton<L, IPredicate>, H, L> abstraction,
				final IIndependenceRelation<IPredicate, L> underlyingIndependence) {
			mRefinableAbstraction = abstraction;
			mUnderlyingIndependence = underlyingIndependence;
		}

		@Override
		public void initialize() {
			mAbstractionLevel = mRefinableAbstraction.getInitial();
		}

		@Override
		public void refine(final IRefinementEngineResult<L, NestedWordAutomaton<L, IPredicate>> refinement) {
			final H newLevel = mRefinableAbstraction.refine(mAbstractionLevel, refinement);
			assert mRefinableAbstraction.getHierarchy().compare(newLevel, mAbstractionLevel)
					.isLessOrEqual() : "Refinement must yield a lower abstraction level";
			mAbstractionLevel = newLevel;
		}

		@Override
		public IIndependenceRelation<IPredicate, L> getOrConstructIndependence() {
			return IndependenceBuilder.fromPredicateActionIndependence(mUnderlyingIndependence)
					// Apply abstraction to each letter before checking commutativity.
					.withAbstraction(mRefinableAbstraction, mAbstractionLevel)
					// Retrieve the constructed relation.
					.build();
		}
	}

	private static class IndependenceContainerForLoopers<L extends IIcfgTransition<?>>
			implements IRefinableIndependenceContainer<L> {

		private final IUltimateServiceProvider mServices;
		private final ILogger mLogger;
		private final CfgSmtToolkit mCsToolkit;
		private final IndependenceSettings.IndependenceType mType;

		private Set<IPredicate> mAbstractionLevel;

		private ChainingHoareTripleChecker mHtc;
		private UnionPredicateCoverageChecker mCoverage;

		public IndependenceContainerForLoopers(final IUltimateServiceProvider services, final CfgSmtToolkit csToolkit,
				final IndependenceSettings.IndependenceType type) {
			mServices = services;
			mLogger = services.getLoggingService().getLogger(IndependenceContainerForLoopers.class);
			mCsToolkit = csToolkit;
			mType = type;
		}

		@Override
		public void initialize() {
			mAbstractionLevel = Collections.emptySet();
			if (mType != IndependenceType.SYNTACTIC) {
				mHtc = ChainingHoareTripleChecker.empty(mLogger);
				mCoverage = UnionPredicateCoverageChecker.empty();
			}
		}

		@Override
		public void refine(final IRefinementEngineResult<L, NestedWordAutomaton<L, IPredicate>> refinement) {
			mAbstractionLevel = LooperIndependenceRelation.refine(mAbstractionLevel, refinement);
			if (mType != IndependenceType.SYNTACTIC) {
				final Predicate<IPredicate> protection = p -> !refinement.getPredicateUnifier().isRepresentative(p);
				mHtc = mHtc.andThen(getHoareTripleChecker(refinement)).predicatesProtectedBy(protection);
				mCoverage = mCoverage.with(refinement.getPredicateUnifier().getCoverageRelation(), protection);
			}
		}

		@Override
		public IIndependenceRelation<IPredicate, L> getOrConstructIndependence() {
			return IndependenceBuilder
					.fromPredicateActionIndependence(
							new LooperIndependenceRelation<>(mAbstractionLevel, constructCheck()))
					.threadSeparated().build();
		}

		private IHoareTripleChecker getHoareTripleChecker(final IRefinementEngineResult<L, ?> refinement) {
			final IHoareTripleChecker refinementHtc = refinement.getHoareTripleChecker();
			if (refinementHtc != null) {
				return refinementHtc;
			}
			return HoareTripleCheckerUtils.constructEfficientHoareTripleCheckerWithCaching(mServices,
					HoareTripleChecks.MONOLITHIC, mCsToolkit, refinement.getPredicateUnifier());
		}

		private ILooperCheck<L> constructCheck() {
			switch (mType) {
			case SEMANTIC:
				return new ILooperCheck.HoareLooperCheck<>(mHtc, mCoverage);
			case SYNTACTIC:
				return new ILooperCheck.IndependentLooperCheck<>();
			default:
				throw new UnsupportedOperationException("Unknown independence type " + mType);
			}
		}
	}
}
