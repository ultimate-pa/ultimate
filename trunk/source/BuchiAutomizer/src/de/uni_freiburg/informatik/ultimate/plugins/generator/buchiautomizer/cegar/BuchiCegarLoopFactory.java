package de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.cegar;

import java.util.Collections;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.IAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.boogie.annotation.LTLPropertyCheck;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.RunningTaskInfo;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.ToolchainCanceledException;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.ToolchainExceptionWrapper;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.BuchiProgramAcceptingStateAnnotation;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.initialabstraction.IInitialAbstractionProvider;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.initialabstraction.NwaInitialAbstractionProvider;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.BuchiCegarLoopBenchmarkGenerator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.RankVarConstructor;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.CegarLoopStatisticsDefinitions;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.PredicateFactoryRefinement;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.WitnessAutomatonAbstractionProvider;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.witnesschecking.WitnessUtils.Property;
import de.uni_freiburg.informatik.ultimate.witnessparser.graph.WitnessEdge;
import de.uni_freiburg.informatik.ultimate.witnessparser.graph.WitnessNode;

public class BuchiCegarLoopFactory<L extends IIcfgTransition<?>> {
	private final BuchiCegarLoopBenchmarkGenerator mCegarLoopBenchmark;
	private final Class<L> mTransitionClazz;

	public BuchiCegarLoopFactory(final Class<L> transitionClazz,
			final BuchiCegarLoopBenchmarkGenerator benchmarkGenerator) {
		mTransitionClazz = transitionClazz;
		mCegarLoopBenchmark = benchmarkGenerator;
	}

	public AbstractBuchiCegarLoop<L, ?> constructCegarLoop(final IIcfg<?> icfg,
			final RankVarConstructor rankVarConstructor, final PredicateFactory predicateFactory,
			final TAPreferences taPrefs, final IUltimateServiceProvider services,
			final INestedWordAutomaton<WitnessEdge, WitnessNode> witnessAutomaton) {
		final PredicateFactoryRefinement stateFactoryForRefinement = new PredicateFactoryRefinement(services,
				rankVarConstructor.getCsToolkitWithRankVariables().getManagedScript(), predicateFactory, false,
				Collections.emptySet());
		final var provider = createAutomataAbstractionProvider(services, predicateFactory, stateFactoryForRefinement,
				witnessAutomaton);
		final var initialAbstraction = constructInitialAbstraction(provider, icfg);
		return new BuchiAutomatonCegarLoop<>(icfg, rankVarConstructor, predicateFactory, taPrefs, services,
				mTransitionClazz, initialAbstraction, stateFactoryForRefinement, mCegarLoopBenchmark);
	}

	private static Set<IcfgLocation> getAcceptingStates(final IIcfg<?> icfg) {
		final Set<IcfgLocation> allStates =
				icfg.getProgramPoints().values().stream().flatMap(x -> x.values().stream()).collect(Collectors.toSet());
		if (LTLPropertyCheck.getAnnotation(icfg) == null) {
			return allStates;
		}
		return allStates.stream().filter(a -> BuchiProgramAcceptingStateAnnotation.getAnnotation(a) != null)
				.collect(Collectors.toSet());
	}

	private IInitialAbstractionProvider<L, ? extends INestedWordAutomaton<L, IPredicate>>
			createAutomataAbstractionProvider(final IUltimateServiceProvider services,
					final PredicateFactory predicateFactory, final PredicateFactoryRefinement stateFactory,
					final INwaOutgoingLetterAndTransitionProvider<WitnessEdge, WitnessNode> witnessAutomaton) {
		final IInitialAbstractionProvider<L, INestedWordAutomaton<L, IPredicate>> provider =
				new NwaInitialAbstractionProvider<>(services, stateFactory, true, predicateFactory);
		if (witnessAutomaton == null) {
			return provider;
		}
		return new WitnessAutomatonAbstractionProvider<>(services, predicateFactory, stateFactory, provider,
				witnessAutomaton, Property.TERMINATION);
	}

	private <A extends IAutomaton<L, IPredicate>> A
			constructInitialAbstraction(final IInitialAbstractionProvider<L, A> provider, final IIcfg<?> icfg) {
		// OverallTime should include InitialAbstractionConstructionTime. Hence we start and stop both stopwatches.
		mCegarLoopBenchmark.start(CegarLoopStatisticsDefinitions.OverallTime);
		mCegarLoopBenchmark.start(CegarLoopStatisticsDefinitions.InitialAbstractionConstructionTime);
		try {
			return provider.getInitialAbstraction(icfg, getAcceptingStates(icfg));
		} catch (final AutomataOperationCanceledException ex) {
			final RunningTaskInfo runningTaskInfo =
					new RunningTaskInfo(this.getClass(), "constructing initial abstraction");
			ex.addRunningTaskInfo(runningTaskInfo);
			throw new ToolchainExceptionWrapper(Activator.PLUGIN_ID, ex);
		} catch (final ToolchainCanceledException ex) {
			final RunningTaskInfo runningTaskInfo =
					new RunningTaskInfo(this.getClass(), "constructing initial abstraction");
			ex.addRunningTaskInfo(runningTaskInfo);
			throw ex;
		} catch (final AutomataLibraryException e) {
			throw new ToolchainExceptionWrapper(Activator.PLUGIN_ID, e);
		} finally {
			mCegarLoopBenchmark.stop(CegarLoopStatisticsDefinitions.InitialAbstractionConstructionTime);
			mCegarLoopBenchmark.stop(CegarLoopStatisticsDefinitions.OverallTime);
		}
	}
}
