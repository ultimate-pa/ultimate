/*
 * Copyright (C) 2017 Christian Schilling (schillic@informatik.uni-freiburg.de)
 * Copyright (C) 2017 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.errorabstraction;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Map.Entry;
import java.util.Queue;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomataUtils;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.IOutgoingTransitionlet;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.IncomingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.IIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IInternalAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hoaretriple.IHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hoaretriple.IHoareTripleChecker.Validity;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hoaretriple.IncrementalHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.IncrementalImplicationChecker;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.PartialQuantifierElimination;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.interpolant.TracePredicates;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.PredicateTransformer;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.TermDomainOperationProvider;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.PredicateFactoryForInterpolantAutomata;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.IterativePredicateTransformer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.IterativePredicateTransformer.IPredicatePostprocessor;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.IterativePredicateTransformer.QuantifierEliminationPostprocessor;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.IterativePredicateTransformer.TraceInterpolationException;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences.InterpolantAutomatonEnhancement;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.DefaultTransFormulas;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.TraceCheckSpWp.UnifyPostprocessor;
import de.uni_freiburg.informatik.ultimate.util.ConstructionCache;
import de.uni_freiburg.informatik.ultimate.util.ConstructionCache.IValueConstruction;
import de.uni_freiburg.informatik.ultimate.util.datastructures.poset.PosetUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Triple;

/**
 * Constructs a danger automaton for a given error trace.
 *
 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
 * @param <LETTER>
 *            letter type in the trace/automaton
 */
class DangerAutomatonBuilder<LETTER extends IIcfgTransition<?>> implements IErrorAutomatonBuilder<LETTER> {
	/**
	 * {@code true} iff predicates are unified.
	 */
	private static final boolean UNIFY_PREDICATES = true;

	private final IUltimateServiceProvider mServices;
	private NestedWordAutomaton<LETTER, IPredicate> mResult;
	private final IPredicate mErrorPrecondition;

	private final Set<IPredicate> mPredicates;

	private final ILogger mLogger;

	private final CfgSmtToolkit mCsTookit;

	private PredicateTransformer<Term, IPredicate, TransFormula> mPt;
	final ConstructionCache<Pair<IPredicate, LETTER>, Term> mPreInternalCc;
	final ConstructionCache<Triple<IPredicate, LETTER, IPredicate>, LBool> mIntersectionWithPreInternalCc;

	private final boolean USE_DISJUNCTIONS = false;

	private IPredicateUnifier mPredicateUnifier;
	Set<HashRelation<LETTER, IPredicate>> constrainersCache = new HashSet<>();

	/**
	 * @param services
	 *            Ultimate services.
	 * @param predicateFactory
	 *            predicate factory
	 * @param predicateUnifier
	 *            predicate unifier
	 * @param csToolkit
	 *            SMT toolkit
	 * @param simplificationTechnique
	 *            simplification technique
	 * @param xnfConversionTechnique
	 *            XNF conversion technique
	 * @param symbolTable
	 *            symbol table
	 * @param predicateFactoryForAutomaton
	 *            predicate factory for the danger automaton (will eventually be removed by a refactoring)
	 * @param abstraction
	 *            current program abstraction
	 * @param trace
	 *            error trace
	 * @param iteration
	 *            CEGAR loop iteration in which this builder was created
	 */
	@SuppressWarnings("squid:S00107")
	public DangerAutomatonBuilder(final IUltimateServiceProvider services, final PredicateFactory predicateFactory,
			final IPredicateUnifier predicateUnifier, final CfgSmtToolkit csToolkit,
			final SimplificationTechnique simplificationTechnique, final XnfConversionTechnique xnfConversionTechnique,
			final IIcfgSymbolTable symbolTable,
			final PredicateFactoryForInterpolantAutomata predicateFactoryForAutomaton,
			final INestedWordAutomaton<LETTER, IPredicate> abstraction, final NestedWord<LETTER> trace) {
		if (!NestedWordAutomataUtils.isFiniteAutomaton(abstraction)) {
			throw new IllegalArgumentException("Calls and returns are not yet supported.");
		}
		mServices = services;
		mLogger = services.getLoggingService().getLogger(Activator.PLUGIN_ID);
		mCsTookit = csToolkit;
		mPredicateUnifier = predicateUnifier;
		final PredicateUnificationMechanism internalPredicateUnifier =
				new PredicateUnificationMechanism(predicateUnifier, UNIFY_PREDICATES);

		final TracePredicates tracePredicates = constructPredicates(mLogger, predicateFactory, internalPredicateUnifier,
				csToolkit, simplificationTechnique, xnfConversionTechnique, symbolTable, trace, predicateUnifier);
		mErrorPrecondition = tracePredicates.getPrecondition();
		mPredicates = collectPredicates(tracePredicates);
		mLogger.info("Constructing danger automaton with " + mPredicates.size() + " predicates.");
		mPt = new PredicateTransformer<>(
				csToolkit.getManagedScript(), new TermDomainOperationProvider(mServices, csToolkit.getManagedScript()));
		final IncrementalHoareTripleChecker htc = new IncrementalHoareTripleChecker(mCsTookit, false);

		{
			final IValueConstruction<Pair<IPredicate, LETTER>, Term> valueConstruction =
					new IValueConstruction<Pair<IPredicate, LETTER>, Term>() {
				@Override
				public Term constructValue(final Pair<IPredicate, LETTER> key) {
					final Term wp = mPt.weakestPrecondition(predicateFactory.not(key.getFirst()), key.getSecond().getTransformula());
					final Term wpLessQuantifiers = PartialQuantifierElimination.tryToEliminate(mServices, mLogger,
							csToolkit.getManagedScript(), wp, SimplificationTechnique.SIMPLIFY_DDA,
							XnfConversionTechnique.BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION);
					final Term pre = SmtUtils.not(csToolkit.getManagedScript().getScript(), wpLessQuantifiers);
					return pre;
				}
			};
			mPreInternalCc = new ConstructionCache<>(valueConstruction);
		}

		{
			final IValueConstruction<Triple<IPredicate, LETTER, IPredicate>, LBool> valueConstruction =
					new IValueConstruction<Triple<IPredicate, LETTER, IPredicate>, LBool>() {

						@Override
						public LBool constructValue(final Triple<IPredicate, LETTER, IPredicate> key) {
							final Validity val = htc.checkInternal(key.getFirst(), (IInternalAction) key.getSecond(),
									predicateFactory.not(key.getThird()));
							htc.releaseLock();
							return IHoareTripleChecker.convertValidity2Lbool(val);
						}
					};
			mIntersectionWithPreInternalCc = new ConstructionCache<>(valueConstruction);
		}


		final NestedWordAutomaton<LETTER, IPredicate> optimizedResult = constructDangerAutomaton(new AutomataLibraryServices(services), mLogger, predicateFactory,
				internalPredicateUnifier, csToolkit, predicateFactoryForAutomaton, abstraction, mPredicates, true);
//		final NestedWordAutomaton<LETTER, IPredicate> unoptimizedResult = constructDangerAutomaton(
//				new AutomataLibraryServices(services), mLogger, predicateFactory, internalPredicateUnifier, csToolkit,
//				predicateFactoryForAutomaton, abstraction, mPredicates, false);
//		try {
//			final Boolean languageIsEquivalent = new IsEquivalent<LETTER, IPredicate>(
//					new AutomataLibraryServices(services), new PredicateFactoryResultChecking(predicateFactory), optimizedResult, unoptimizedResult)
//							.getResult();
//			if (!languageIsEquivalent) {
//				throw new AssertionError("language not equivalent");
//			}
//		} catch (final AutomataLibraryException e) {
//			throw new AssertionError(e);
//		}
		mResult = optimizedResult;
	}

	@Override
	public ErrorAutomatonType getType() {
		return ErrorAutomatonType.DANGER_AUTOMATON;
	}

	@Override
	public NestedWordAutomaton<LETTER, IPredicate> getResultBeforeEnhancement() {
		return mResult;
	}

	@Override
	public INwaOutgoingLetterAndTransitionProvider<LETTER, IPredicate> getResultAfterEnhancement() {
		return mResult;
	}

	@Override
	public IPredicate getErrorPrecondition() {
		return mErrorPrecondition;
	}

	@Override
	public InterpolantAutomatonEnhancement getEnhancementMode() {
		return InterpolantAutomatonEnhancement.NONE;
	}

	private NestedWordAutomaton<LETTER, IPredicate> constructDangerAutomaton(final AutomataLibraryServices services,
			final ILogger logger, final PredicateFactory predicateFactory,
			final PredicateUnificationMechanism predicateUnifier, final CfgSmtToolkit csToolkit,
			final PredicateFactoryForInterpolantAutomata predicateFactoryForAutomaton,
			final INestedWordAutomaton<LETTER, IPredicate> abstraction, final Set<IPredicate> predicates, final boolean constructMinimalCover) {
		final HashRelation<IPredicate, IPredicate> abstState2dangStates = new HashRelation<>();
		final ConstructionCache<Pair<IPredicate, Set<IPredicate>>, IPredicate> disjunctionProvider;
		{
			final IValueConstruction<Pair<IPredicate, Set<IPredicate>>, IPredicate> valueConstruction = new IValueConstruction<Pair<IPredicate, Set<IPredicate>>, IPredicate>() {
				@Override
				public IPredicate constructValue(final Pair<IPredicate, Set<IPredicate>> key) {
					return predicateFactory.or(false, key.getSecond());
				}
			};
			disjunctionProvider = new ConstructionCache<>(valueConstruction);
		}
		final IncrementalImplicationChecker ic =
				new IncrementalImplicationChecker(mServices, csToolkit.getManagedScript());

		final ConstructionCache<HashRelation<LETTER, IPredicate>, Set<IPredicate>> coveredPredicatesProvider;
		{
			final IValueConstruction<HashRelation<LETTER, IPredicate>, Set<IPredicate>> valueConstruction = new IValueConstruction<HashRelation<LETTER,IPredicate>, Set<IPredicate>>() {

				@Override
				public Set<IPredicate> constructValue(final HashRelation<LETTER, IPredicate> constrainers) {
					final Set<Term> programStatesWithSucc_Term = new HashSet<>();
					for (final Entry<LETTER, IPredicate> entry : constrainers.entrySet()) {
						final Term pre = mPreInternalCc.getOrConstruct(new Pair<IPredicate, LETTER>(entry.getValue(), entry.getKey()));
						programStatesWithSucc_Term.add(pre);
					}
					final IPredicate programStatesWithSucc_Pred = predicateFactory
							.newPredicate(SmtUtils.or(csToolkit.getManagedScript().getScript(), programStatesWithSucc_Term));

					final Set<IPredicate> coveredPredicates = new HashSet<>();
					try {
						for (final IPredicate candidate : predicates) {
							if (!coveredPredicates.contains(candidate)) {
								final Validity icres = ic.checkImplication(candidate, programStatesWithSucc_Pred);
								if (icres == Validity.VALID) {
									//coveredPredicates.add(candidate);
									coveredPredicates.addAll(mPredicateUnifier.getCoverageRelation().getCoveredPredicates(candidate));
								}
							}
						}
					} finally {
						ic.releaseLock();
					}
					return coveredPredicates;
				}
			};
			coveredPredicatesProvider = new ConstructionCache<>(valueConstruction);

		}





		final Queue<IPredicate> worklist = new ArrayDeque<>();

		final NestedWordAutomaton<LETTER, IPredicate> result = new NestedWordAutomaton<>(services,
				NestedWordAutomataUtils.getVpAlphabet(abstraction), predicateFactoryForAutomaton);

		final IPredicate trueState = predicateUnifier.getTruePredicate();
		for (final IPredicate state : abstraction.getFinalStates()) {
			result.addState(false, true,
					disjunctionProvider.getOrConstruct(new Pair<>(state, Collections.singleton(trueState))));
			abstState2dangStates.addPair(state, trueState);
			worklist.add(state);
		}

		final PredicateTransformer<Term, IPredicate, TransFormula> pt = new PredicateTransformer<>(
				csToolkit.getManagedScript(), new TermDomainOperationProvider(mServices, csToolkit.getManagedScript()));


		while (!worklist.isEmpty()) {
			final IPredicate state = worklist.poll();
			for (final IncomingInternalTransition<LETTER, IPredicate> in : abstraction.internalPredecessors(state)) {
				final IPredicate pred = in.getPred();
				Set<IPredicate> coveredPredicates = getCoveredPredicates(logger, predicateFactory, csToolkit,
						abstraction, abstState2dangStates, disjunctionProvider, predicates, pt, ic, pred, coveredPredicatesProvider);
				if (coveredPredicates.isEmpty()) {
					continue;
					// no need to proceed in this iteration, a state labeled with false will not help us
				}
				if (constructMinimalCover) {
					final Set<IPredicate> minimalCover = PosetUtils
							.filterMaximalElements(coveredPredicates,
									mPredicateUnifier.getCoverageRelation().getPartialComperator())
							.collect(Collectors.toSet());
					if (minimalCover.size() < coveredPredicates.size()) {
//						mLogger.warn("can save " + (coveredPredicates.size() - minimalCover.size()) + " predicates");
						coveredPredicates = minimalCover;
					}
				}

				if (USE_DISJUNCTIONS) {
					final IPredicate newState = getNewState(abstraction, abstState2dangStates, disjunctionProvider,
							worklist, result, pred, coveredPredicates);
					addOutgoingTransitionsToContributingStates(logger, predicateFactory, csToolkit, abstraction,
							abstState2dangStates, disjunctionProvider, result, pt, pred, newState);
				} else {
					final Set<IPredicate> currentStatesInDanger = abstState2dangStates.getImage(pred);
					boolean thereWasNewPredicate = false;
					for (final IPredicate covered : coveredPredicates) {
						if (!currentStatesInDanger.contains(covered)) {
							thereWasNewPredicate = true;

							final IPredicate newState = disjunctionProvider
									.getOrConstruct(new Pair<>(pred, Collections.singleton(covered)));
							final boolean isInitial = abstraction.isInitial(pred);
							final boolean isFinal = abstraction.isFinal(pred);
							result.addState(isInitial, isFinal, newState);

							abstState2dangStates.addPair(pred, covered);
						}
					}
					if (thereWasNewPredicate) {
						worklist.add(pred);
					}

					for (final IPredicate covered : coveredPredicates) {
						for (final OutgoingInternalTransition<LETTER, IPredicate> out : abstraction.internalSuccessors(pred)) {
							for (final IPredicate succInDanger : abstState2dangStates.getImage(out.getSucc())) {
								final LBool isContributing = mIntersectionWithPreInternalCc.getOrConstruct(new Triple<IPredicate, LETTER, IPredicate>(covered, out.getLetter(), succInDanger));
								if (isContributing == LBool.SAT) {
									result.addInternalTransition(disjunctionProvider.getOrConstruct(new Pair<>(pred, Collections.singleton(covered))),
											out.getLetter(),
											disjunctionProvider.getOrConstruct(new Pair<>(out.getSucc(), Collections.singleton(succInDanger))));
								}
							}
						}

					}
				}
			}
		}

		return result;
	}

	private Set<IPredicate> getCoveredPredicates(final ILogger logger, final PredicateFactory predicateFactory,
			final CfgSmtToolkit csToolkit, final INestedWordAutomaton<LETTER, IPredicate> abstraction,
			final HashRelation<IPredicate, IPredicate> abstState2dangStates,
			final ConstructionCache<Pair<IPredicate, Set<IPredicate>>, IPredicate> disjunctionProvider,
			final Set<IPredicate> predicates, final PredicateTransformer<Term, IPredicate, TransFormula> pt,
			final IncrementalImplicationChecker ic, final IPredicate pred, final ConstructionCache<HashRelation<LETTER, IPredicate>, Set<IPredicate>> coveredPredicatesProvider) {

		final HashRelation<LETTER, IPredicate> constrainers = new HashRelation<>();
		for (final OutgoingInternalTransition<LETTER, IPredicate> out : abstraction.internalSuccessors(pred)) {
			for (final IPredicate succInDanger : abstState2dangStates.getImage(out.getSucc())) {
				constrainers.addPair(out.getLetter(), succInDanger);
			}
		}
		return coveredPredicatesProvider.getOrConstruct(constrainers);
	}

	private IPredicate getNewState(final INestedWordAutomaton<LETTER, IPredicate> abstraction,
			final HashRelation<IPredicate, IPredicate> abstState2dangStates,
			final ConstructionCache<Pair<IPredicate, Set<IPredicate>>, IPredicate> resultStateProvider,
			final Queue<IPredicate> worklist, final NestedWordAutomaton<LETTER, IPredicate> result,
			final IPredicate pred, final Set<IPredicate> coveredPredicates) {
		final Set<IPredicate> oldAbstraction = abstState2dangStates.getImage(pred);
		if (coveredPredicates.equals(oldAbstraction)) {
			// do nothing
			return resultStateProvider.getOrConstruct(new Pair<>(pred, oldAbstraction));
		}

		// predicate changed
		// we have to "backtrack" (want to try if we can computer better predecessors)
		if (!worklist.contains(pred)) {
			worklist.add(pred);
		}

		final IPredicate newState = resultStateProvider.getOrConstruct(new Pair<>(pred, coveredPredicates));
		final boolean isInitial = abstraction.isInitial(pred);
		final boolean isFinal = abstraction.isFinal(pred);
		result.addState(isInitial, isFinal, newState);
		if (!oldAbstraction.isEmpty()) {
			final IPredicate oldstate = resultStateProvider.getOrConstruct(new Pair<>(pred, oldAbstraction));
			// there was already a state, we have to copy all its incoming transitions and remove it
			assert result.contains(oldstate);
			copyAllIncomingTransitions(oldstate, newState, result);
			result.removeState(oldstate);
		}
		for (final IPredicate p : coveredPredicates) {
			abstState2dangStates.addPair(pred, p);
		}
		return newState;
	}

	/* add outgoing transitions to all successors that finally contributed
	 *(i.e., where the intersection of pre with the abstract state is not empty)
	 */
	private void addOutgoingTransitionsToContributingStates(final ILogger logger,
			final PredicateFactory predicateFactory, final CfgSmtToolkit csToolkit,
			final INestedWordAutomaton<LETTER, IPredicate> abstraction,
			final HashRelation<IPredicate, IPredicate> abstState2dangStates,
			final ConstructionCache<Pair<IPredicate, Set<IPredicate>>, IPredicate> disjunctionProvider,
			final NestedWordAutomaton<LETTER, IPredicate> result,
			final PredicateTransformer<Term, IPredicate, TransFormula> pt, final IPredicate pred,
			final IPredicate newState) {
		for (final OutgoingInternalTransition<LETTER, IPredicate> out : abstraction.internalSuccessors(pred)) {
			final IPredicate succInDanger = getSuccessorDisjunction(abstState2dangStates, disjunctionProvider, out);
			if (succInDanger == null) {
				// successor state does not (yet?) have corresponding predicate
				continue;
			}
			assert result.getStates().contains(succInDanger);
			final LBool checkSatRes;
			checkSatRes = mIntersectionWithPreInternalCc.getOrConstruct(
					new Triple<IPredicate, LETTER, IPredicate>(newState, out.getLetter(), succInDanger));
			if (checkSatRes != LBool.UNSAT) {
				// edge probably (result might be unknown) contributed, so we add it
				result.addInternalTransition(newState, out.getLetter(), succInDanger);
				// Matthias: maybe this crashes and we have to check if edge was already added
			}
		}
	}

	/**
	 * Check if the intersection between "predecessor and pre("successor",st)
	 * is satisfiable.
	 */
	private LBool checkIntersectionWithPre(final ILogger logger, final PredicateFactory predicateFactory,
			final CfgSmtToolkit csToolkit, final PredicateTransformer<Term, IPredicate, TransFormula> pt,
			final IPredicate predecessor, final OutgoingInternalTransition<LETTER, IPredicate> out,
			final IPredicate successor) {
		final Term pre = mPreInternalCc.getOrConstruct(new Pair<IPredicate, LETTER>(successor, out.getLetter()));
		final Term conjunction = SmtUtils.and(csToolkit.getManagedScript().getScript(),
				Arrays.asList(new Term[] { pre, predecessor.getFormula() }));
		final LBool checkSatRes = SmtUtils.checkSatTerm(csToolkit.getManagedScript().getScript(), conjunction);
		return checkSatRes;
	}

	private IPredicate getSuccessorDisjunction(final HashRelation<IPredicate, IPredicate> abstState2dangStates,
			final ConstructionCache<Pair<IPredicate, Set<IPredicate>>, IPredicate> disjunctionProvider,
			final IOutgoingTransitionlet<LETTER, IPredicate> out) {
		final IPredicate succInAbstraction = out.getSucc();
		final Set<IPredicate> succDisjunctionInDanger = abstState2dangStates.getImage(succInAbstraction);
		if (succDisjunctionInDanger.isEmpty()) {
			// successor state does not (yet?) have corresponding predicate
			return null;
		}
		return disjunctionProvider.getOrConstruct(new Pair<>(succInAbstraction, succDisjunctionInDanger));
	}



	private TracePredicates constructPredicates(final ILogger logger, final PredicateFactory predicateFactory,
			final PredicateUnificationMechanism pum, final CfgSmtToolkit csToolkit,
			final SimplificationTechnique simplificationTechnique, final XnfConversionTechnique xnfConversionTechnique,
			final IIcfgSymbolTable symbolTable, final NestedWord<LETTER> trace, final IPredicateUnifier predicateUnifier) throws AssertionError {
		final IterativePredicateTransformer ipt = new IterativePredicateTransformer(predicateFactory,
				csToolkit.getManagedScript(), csToolkit.getModifiableGlobalsTable(), mServices, trace, null,
				pum.getTruePredicate(), null, pum.getTruePredicate(),
				simplificationTechnique, xnfConversionTechnique, symbolTable);
		final List<IPredicatePostprocessor> postprocessors = new ArrayList<>();
		final QuantifierEliminationPostprocessor qepp = new QuantifierEliminationPostprocessor(mServices, logger,
				csToolkit.getManagedScript(), predicateFactory, simplificationTechnique, xnfConversionTechnique);
		postprocessors.add(qepp);
		postprocessors.add(new UnifyPostprocessor(predicateUnifier));
		final DefaultTransFormulas dtf = new DefaultTransFormulas(trace, null, null, Collections.emptySortedMap(),
				csToolkit.getOldVarsAssignmentCache(), false);
		try {
			return ipt.computePreSequence(dtf, postprocessors, false);
		} catch (final TraceInterpolationException e) {
			throw new AssertionError("failed to compute sequence " + e);
		}
	}

	private static Set<IPredicate> collectPredicates(final TracePredicates tracePredicates) {
		final Set<IPredicate> predicates = new HashSet<>(tracePredicates.getPredicates());
		predicates.add(tracePredicates.getPostcondition());
		predicates.add(tracePredicates.getPrecondition());
		return predicates;
	}

	private void copyAllIncomingTransitions(final IPredicate oldstate, final IPredicate newState,
			final NestedWordAutomaton<LETTER, IPredicate> result) {
		for (final IncomingInternalTransition<LETTER, IPredicate> in : result.internalPredecessors(oldstate)) {
			result.addInternalTransition(in.getPred(), in.getLetter(), newState);
		}
	}
}
