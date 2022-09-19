package de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.cegar;

import java.util.ArrayList;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.BuchiComplementFKV;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.NestedLassoRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.IStateDeterminizer;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.PowersetDeterminizer;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNetTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.PetriNetLassoRun;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.PetriNetNot1SafeException;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.PetriNetRun;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.operations.DifferencePairwiseOnDemand;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.operations.IntersectBuchiLazy;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.BuchiUnfolder;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.BuchiCegarLoopBenchmarkGenerator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.RankVarConstructor;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.Minimization;

public class BuchiPetriNetCegarLoopLazy<L extends IIcfgTransition<?>>
		extends AbstractBuchiCegarLoop<L, IPetriNetTransitionProvider<L, IPredicate>> {
	private final Marking2MLPredicate mMarking2MLPredicate;

	public BuchiPetriNetCegarLoopLazy(final IIcfg<?> icfg, final RankVarConstructor rankVarConstructor,
			final PredicateFactory predicateFactory, final TAPreferences taPrefs,
			final IUltimateServiceProvider services, final Class<L> transitionClazz,
			final IPetriNetTransitionProvider<L, IPredicate> initialAbstraction,
			final BuchiCegarLoopBenchmarkGenerator benchmarkGenerator) {
		super(icfg, rankVarConstructor, predicateFactory, taPrefs, services, transitionClazz, initialAbstraction,
				benchmarkGenerator);
		mMarking2MLPredicate = new Marking2MLPredicate(predicateFactory);
	}

	@Override
	protected boolean isAbstractionEmpty(final IPetriNetTransitionProvider<L, IPredicate> abstraction)
			throws AutomataLibraryException {
		final var unfolder = new BuchiUnfolder<>(new AutomataLibraryServices(mServices), abstraction,
				mPref.eventOrder(), mPref.cutOffRequiresSameTransition(), true);
		final PetriNetLassoRun<L, IPredicate> run = unfolder.getAcceptingRun();
		if (run == null) {
			return true;
		}
		mCounterexample =
				new NestedLassoRun<>(constructNestedLassoRun(run.getStem()), constructNestedLassoRun(run.getLoop()));
		return false;
	}

	private NestedRun<L, IPredicate> constructNestedLassoRun(final PetriNetRun<L, IPredicate> run) {
		return new NestedRun<>(NestedWord.nestedWord(run.getWord()), (ArrayList<IPredicate>) run.getStateSequence()
				.stream().map(mMarking2MLPredicate::markingToPredicate).collect(Collectors.toList()));
	}

	@Override
	protected IPetriNetTransitionProvider<L, IPredicate> refineFinite(
			final IPetriNetTransitionProvider<L, IPredicate> abstraction,
			final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> interpolantAutomaton)
			throws AutomataLibraryException {
		try {
			return new DifferencePairwiseOnDemand<>(new AutomataLibraryServices(mServices), abstraction,
					interpolantAutomaton).getResult();
		} catch (AutomataOperationCanceledException | PetriNetNot1SafeException e) {
			throw new AutomataLibraryException(getClass(), e.toString());
		}
	}

	@Override
	protected IPetriNetTransitionProvider<L, IPredicate> refineBuchi(
			final IPetriNetTransitionProvider<L, IPredicate> abstraction,
			final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> interpolantAutomaton)
			throws AutomataLibraryException {
		final IStateDeterminizer<L, IPredicate> stateDeterminizer =
				new PowersetDeterminizer<>(interpolantAutomaton, mUseDoubleDeckers, mDefaultStateFactory);
		final BuchiComplementFKV<L, IPredicate> complNwa = new BuchiComplementFKV<>(
				new AutomataLibraryServices(mServices), mDefaultStateFactory, interpolantAutomaton, stateDeterminizer);
		mBenchmarkGenerator.reportHighestRank(complNwa.getHighestRank());
		return new IntersectBuchiLazy<>(abstraction, complNwa.getResult(), mDefaultStateFactory);
	}

	@Override
	protected IPetriNetTransitionProvider<L, IPredicate> reduceAbstractionSize(
			final IPetriNetTransitionProvider<L, IPredicate> abstraction, final Minimization automataMinimization)
			throws AutomataOperationCanceledException {
		return abstraction;
	}

}
