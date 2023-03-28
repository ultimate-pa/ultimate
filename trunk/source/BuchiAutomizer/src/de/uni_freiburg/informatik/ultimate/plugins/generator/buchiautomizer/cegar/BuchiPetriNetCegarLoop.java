package de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.cegar;

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
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.PetriNetLassoRun;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.PetriNetNot1SafeException;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.PetriNetRun;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.BoundedPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.operations.DifferencePairwiseOnDemand;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.operations.IntersectBuchiEager;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.BuchiIsEmpty;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.BuchiCegarLoopBenchmarkGenerator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.RankVarConstructor;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.Minimization;

public class BuchiPetriNetCegarLoop<L extends IIcfgTransition<?>>
		extends AbstractBuchiCegarLoop<L, IPetriNet<L, IPredicate>> {
	private final Marking2MLPredicate mMarking2MLPredicate;

	public BuchiPetriNetCegarLoop(final IIcfg<?> icfg, final RankVarConstructor rankVarConstructor,
			final PredicateFactory predicateFactory, final TAPreferences taPrefs,
			final IUltimateServiceProvider services, final Class<L> transitionClazz,
			final IPetriNet<L, IPredicate> initialAbstraction,
			final BuchiCegarLoopBenchmarkGenerator benchmarkGenerator) {
		super(icfg, rankVarConstructor, predicateFactory, taPrefs, services, transitionClazz, initialAbstraction,
				benchmarkGenerator);
		mMarking2MLPredicate = new Marking2MLPredicate(predicateFactory);
	}

	@Override
	protected boolean isAbstractionEmpty(final IPetriNet<L, IPredicate> abstraction) throws AutomataLibraryException {
		final var isempty = new BuchiIsEmpty<>(new AutomataLibraryServices(mServices), abstraction, mPref.eventOrder(),
				mPref.cutOffRequiresSameTransition(), true);
		final PetriNetLassoRun<L, IPredicate> run = isempty.getRun();
		// assert isempty.checkResult(new PredicateFactoryResultChecking(mPredicateFactory));
		if (run == null) {
			return true;
		}
		mCounterexample =
				new NestedLassoRun<>(constructNestedLassoRun(run.getStem()), constructNestedLassoRun(run.getLoop()));
		return false;
	}

	private NestedRun<L, IPredicate> constructNestedLassoRun(final PetriNetRun<L, IPredicate> run) {
		return new NestedRun<>(NestedWord.nestedWord(run.getWord()), run.getStateSequence().stream()
				.map(mMarking2MLPredicate::markingToPredicate).collect(Collectors.toList()));
	}

	@Override
	protected IPetriNet<L, IPredicate> refineFinite(final IPetriNet<L, IPredicate> abstraction,
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
	protected IPetriNet<L, IPredicate> refineBuchi(final IPetriNet<L, IPredicate> abstraction,
			final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> interpolantAutomaton)
			throws AutomataLibraryException {
		final IStateDeterminizer<L, IPredicate> stateDeterminizer =
				new PowersetDeterminizer<>(interpolantAutomaton, mUseDoubleDeckers, mDefaultStateFactory);
		final BuchiComplementFKV<L, IPredicate> complNwa = new BuchiComplementFKV<>(
				new AutomataLibraryServices(mServices), mDefaultStateFactory, interpolantAutomaton, stateDeterminizer);
		mBenchmarkGenerator.reportHighestRank(complNwa.getHighestRank());

		final IntersectBuchiEager<L, IPredicate> intersection = new IntersectBuchiEager<>(
				new AutomataLibraryServices(mServices), mDefaultStateFactory, abstraction, complNwa.getResult());
		return intersection.getResult();
	}

	@Override
	protected IPetriNet<L, IPredicate> reduceAbstractionSize(final IPetriNet<L, IPredicate> abstraction,
			final Minimization automataMinimization) throws AutomataOperationCanceledException {
		BoundedPetriNet<L, IPredicate> reducedNet;
		try {
			// reducedNet = new de.uni_freiburg.informatik.ultimate.automata.petrinet.operations.RemoveUnreachable<>(
			// new AutomataLibraryServices(mServices), abstraction).getResult();
			reducedNet = new de.uni_freiburg.informatik.ultimate.automata.petrinet.operations.RemoveDeadBuchi<>(
					new AutomataLibraryServices(mServices), abstraction, null).getResult();
			// reducedNet = new RemoveRedundantFlow<>(new AutomataLibraryServices(mServices), reducedNet, null, null,
			// null)
			// .getResult();
			return reducedNet;
		} catch (AutomataOperationCanceledException | PetriNetNot1SafeException e) {
			e.printStackTrace();
			mLogger.warn(
					"Unhandled " + e + "occured during abstarction size reduction. Continuing with non-reduced net");
			return abstraction;
		}
	}
}
