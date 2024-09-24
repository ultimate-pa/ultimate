package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.independence;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.function.BiFunction;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.IRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.VpAlphabet;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.IDfsOrder;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.independence.IIndependenceRelation;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IEmptyStackStateFactory;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.interpolant.QualifiedTracePredicates;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.tracehandling.IRefinementEngineResult.BasicRefinementEngineResult;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.tracehandling.IRefinementStrategy;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.SleepSetStateFactoryForRefinement.SleepPredicate;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.util.Lazy;

public class ConditionalCommutativityCounterexampleChecker<L extends IAction> {
	private final IUltimateServiceProvider mServices;
	private final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> mAbstraction;
	private final IEmptyStackStateFactory<IPredicate> mEmptyStackStateFactory;
	private final ConditionalCommutativityChecker<L> mChecker;
	private final IConditionalCommutativityCheckerStatisticsUtils mStatisticsUtils;
	private IRun<L, IPredicate> mRun;
	private final IIndependenceRelation<IPredicate, L> mIndependenceRelation;
	private final IDfsOrder<L, IPredicate> mDFSOrder;

	public ConditionalCommutativityCounterexampleChecker(final IUltimateServiceProvider services,
			final IConditionalCommutativityCriterion<L> criterion,
			final IIndependenceRelation<IPredicate, L> independenceRelation, final IDfsOrder<L, IPredicate> DFSOrder,
			final ManagedScript script, final IIndependenceConditionGenerator generator,
			final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> abstraction,
			final IEmptyStackStateFactory<IPredicate> emptyStackStateFactory,
			final BiFunction<IRun<L, IPredicate>, IPredicate, IRefinementStrategy<L>> buildStrategy,
			final IConditionalCommutativityCheckerStatisticsUtils statisticsUtils) {
		mServices = services;
		mIndependenceRelation = independenceRelation;
		mDFSOrder = DFSOrder;
		mAbstraction = abstraction;
		mEmptyStackStateFactory = emptyStackStateFactory;
		mChecker = new ConditionalCommutativityChecker<>(services, criterion, independenceRelation, script, generator,
				buildStrategy, statisticsUtils);
		mStatisticsUtils = statisticsUtils;
	}

	public BasicRefinementEngineResult<L, NestedWordAutomaton<L, IPredicate>>
			getInterpolants(final IRun<L, IPredicate> run, final List<IPredicate> runPredicates) {
		mRun = run;

		for (int i = 0; i < mRun.getStateSequence().size() - 2; i++) {
			final IPredicate state = mRun.getStateSequence().get(i);
			final L letter1 = mRun.getWord().getSymbol(i);
			final L letter2 = mRun.getWord().getSymbol(i + 1);

			// TODO this is brittle, it will not work for many configurations
			if (((SleepPredicate<L>) state).getSleepSet().contains(letter2)
					|| (mDFSOrder.getOrder(state).compare(letter1, letter2) > 0)) {

				final IPredicate runPredicate = runPredicates.get(i);
				final List<IPredicate> interpolantPredicates = new ArrayList<>();
				if (runPredicate != null && !SmtUtils.isTrueLiteral(runPredicate.getFormula())) {
					interpolantPredicates.add(runPredicate);
				}
				NestedRun<L, IPredicate> currentRun = (NestedRun<L, IPredicate>) mRun;
				if (i != mRun.getStateSequence().size() - 1) {
					currentRun = currentRun.getSubRun(0, i);
				}

				final var refinementResult = mChecker.checkConditionalCommutativity(currentRun, interpolantPredicates,
						state, letter1, letter2);

				if (refinementResult != null) {
					final var predicateUnifier = refinementResult.getPredicateUnifier();
					mStatisticsUtils.addIAIntegration();
					final NestedWordAutomaton<L, IPredicate> automaton =
							constructInterpolantAutomaton(refinementResult.getInfeasibilityProof());

					if (!automaton.contains(predicateUnifier.getFalsePredicate())) {
						automaton.addState(false, true, predicateUnifier.getFalsePredicate());
					}

					final BasicRefinementEngineResult<L, NestedWordAutomaton<L, IPredicate>> newRefinementResult =
							new BasicRefinementEngineResult<>(LBool.UNSAT, automaton, null, false,
									refinementResult.getUsedTracePredicates(), new Lazy<>(null),
									new Lazy<>(predicateUnifier));
					return newRefinementResult;
				}
			}
		}

		return null;
	}

	private NestedWordAutomaton<L, IPredicate>
			constructInterpolantAutomaton(final Collection<QualifiedTracePredicates> proofs) {
		final Set<L> alphabet = new HashSet<>();
		alphabet.addAll(mAbstraction.getAlphabet());
		final VpAlphabet<L> vpAlphabet = new VpAlphabet<>(alphabet);
		final NestedWordAutomaton<L, IPredicate> automaton =
				new NestedWordAutomaton<>(new AutomataLibraryServices(mServices), vpAlphabet, mEmptyStackStateFactory);

		for (final var qtp : proofs) {
			final var tracePredicates = qtp.getTracePredicates();
			automaton.addState(true, false, tracePredicates.getPrecondition());
			final var predicates = tracePredicates.getPredicates();
			for (int i = 0; i < predicates.size(); i++) {
				final IPredicate succPred = predicates.get(i);
				if (!automaton.contains(succPred)) {
					automaton.addState(false, false, succPred);
				}
				final var prev = i == 0 ? tracePredicates.getPrecondition() : predicates.get(i - 1);
				automaton.addInternalTransition(prev, mRun.getWord().getSymbol(i), succPred);
			}
			if (!automaton.contains(tracePredicates.getPostcondition())) {
				automaton.addState(false, false, tracePredicates.getPostcondition());
			}
			automaton.addInternalTransition(predicates.get(predicates.size() - 1),
					mRun.getWord().getSymbol(predicates.size()), tracePredicates.getPostcondition());
		}

		return automaton;
	}

}
