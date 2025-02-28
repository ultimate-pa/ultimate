package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.initialabstraction;

import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.fairness.ActionFairnessAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.fairness.FairProgramAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.fairness.GuardedBuchiIntersection;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.RemoveNonLiveStates;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

public class FairnessInitialAbstractionProvider<L extends IIcfgTransition<?>>
		implements IInitialAbstractionProvider<L, INwaOutgoingLetterAndTransitionProvider<L, IPredicate>> {
	private final IInitialAbstractionProvider<L, ? extends INwaOutgoingLetterAndTransitionProvider<L, IPredicate>> mUnderlying;
	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;

	private static final boolean LAZY = false;

	public FairnessInitialAbstractionProvider(
			final IInitialAbstractionProvider<L, ? extends INwaOutgoingLetterAndTransitionProvider<L, IPredicate>> underlying,
			final IUltimateServiceProvider services, final ILogger logger) {
		mUnderlying = underlying;
		mServices = services;
		mLogger = logger;
	}

	@Override
	public INwaOutgoingLetterAndTransitionProvider<L, IPredicate>
			getInitialAbstraction(final IIcfg<? extends IcfgLocation> icfg, final Set<? extends IcfgLocation> errorLocs)
					throws AutomataLibraryException {
		final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> programAutomaton =
				mUnderlying.getInitialAbstraction(icfg, errorLocs);
		final HashRelation<String, L> threads2Actions = new HashRelation<>();
		final Set<L> alphabet = programAutomaton.getAlphabet();
		// TODO: Should we consider joins belonging to two threads?
		for (final L letter : alphabet) {
			threads2Actions.addPair(letter.getPrecedingProcedure(), letter);
		}
		final var fairThreadAutomata = threads2Actions.getDomain().stream()
				.map(thread -> new ActionFairnessAutomaton<>(alphabet, threads2Actions.getImage(thread))).toList();
		final var fairAutomaton = new GuardedBuchiIntersection<>(fairThreadAutomata,
				x -> x.stream().flatMap(y -> y.stream()).collect(Collectors.toSet()));
		final var result = new FairProgramAutomaton<>(programAutomaton, fairAutomaton,
				new FairnessStateFactory<>(programAutomaton, mServices, icfg.getCfgSmtToolkit().getManagedScript(),
						icfg.getCfgSmtToolkit().getSymbolTable(), mLogger));
		if (LAZY) {
			return result;
		}
		final var eagerProgramAutomaton =
				new RemoveNonLiveStates<>(new AutomataLibraryServices(mServices), programAutomaton).getResult();
		final var eagerProduct = new RemoveNonLiveStates<>(new AutomataLibraryServices(mServices), result).getResult();
		mLogger.warn("Original program automaton: " + eagerProgramAutomaton.sizeInformation());
		mLogger.warn("Fair program automaton: " + eagerProduct.sizeInformation());
		return eagerProduct;
	}
}
