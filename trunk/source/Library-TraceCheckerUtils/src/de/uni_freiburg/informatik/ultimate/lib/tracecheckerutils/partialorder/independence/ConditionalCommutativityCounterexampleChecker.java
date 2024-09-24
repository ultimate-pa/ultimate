package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.independence;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

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
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.interpolant.TracePredicates;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.tracehandling.IRefinementEngineResult.BasicRefinementEngineResult;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.ITraceChecker;
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
			final IEmptyStackStateFactory<IPredicate> emptyStackStateFactory, final ITraceChecker<L> traceChecker,
			final IConditionalCommutativityCheckerStatisticsUtils statisticsUtils) {
		mServices = services;
		mIndependenceRelation = independenceRelation;
		mDFSOrder = DFSOrder;
		mAbstraction = abstraction;
		mEmptyStackStateFactory = emptyStackStateFactory;
		mChecker = new ConditionalCommutativityChecker<>(criterion, independenceRelation, script, generator,
				traceChecker, statisticsUtils);
		mStatisticsUtils = statisticsUtils;
	}

	public BasicRefinementEngineResult<L, NestedWordAutomaton<L, IPredicate>> getInterpolants(
			final IRun<L, IPredicate> run, final List<IPredicate> runPredicates,
			final IPredicateUnifier predicateUnifier) {
		mRun = run;

		for (int i = 0; i < mRun.getStateSequence().size() - 2; i++) {
			final IPredicate state = mRun.getStateSequence().get(i);
			final L letter1 = mRun.getWord().getSymbol(i);
			final L letter2 = mRun.getWord().getSymbol(i + 1);

			if (((SleepPredicate<L>) state).getAnnotation().contains(letter2)
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

				final TracePredicates tracePredicates = mChecker.checkConditionalCommutativity(currentRun,
						interpolantPredicates, state, letter1, letter2);

				final List<IPredicate> conPredicates = new ArrayList<>();
				if (tracePredicates != null) {
					conPredicates.add(tracePredicates.getPrecondition());
					conPredicates.addAll(tracePredicates.getPredicates());
					conPredicates.add(tracePredicates.getPostcondition());
					mStatisticsUtils.addIAIntegration();
					final NestedWordAutomaton<L, IPredicate> automaton = constructInterpolantAutomaton(conPredicates);

					if (!automaton.contains(predicateUnifier.getFalsePredicate())) {
						automaton.addState(false, true, predicateUnifier.getFalsePredicate());
					}

					final BasicRefinementEngineResult<L, NestedWordAutomaton<L, IPredicate>> refinementResult =
							new BasicRefinementEngineResult<>(LBool.UNSAT, automaton, null, false,
									List.of(new QualifiedTracePredicates(tracePredicates, getClass(), false)),
									new Lazy<>(() -> null), new Lazy<>(() -> predicateUnifier));

					return refinementResult;
				}
			}
		}

		return null;
	}

	private NestedWordAutomaton<L, IPredicate> constructInterpolantAutomaton(final List<IPredicate> conPredicates) {
		final Set<L> alphabet = new HashSet<>();
		alphabet.addAll(mAbstraction.getAlphabet());
		final VpAlphabet<L> vpAlphabet = new VpAlphabet<>(alphabet);
		final NestedWordAutomaton<L, IPredicate> automaton =
				new NestedWordAutomaton<>(new AutomataLibraryServices(mServices), vpAlphabet, mEmptyStackStateFactory);

		automaton.addState(true, false, conPredicates.get(0));
		for (Integer i = 1; i < conPredicates.size(); i++) {
			final IPredicate succPred = conPredicates.get(i);
			if (!automaton.contains(succPred)) {
				automaton.addState(false, false, succPred);
			}
			automaton.addInternalTransition(conPredicates.get(i - 1), mRun.getWord().getSymbol(i - 1), succPred);
		}
		return automaton;
	}

}
