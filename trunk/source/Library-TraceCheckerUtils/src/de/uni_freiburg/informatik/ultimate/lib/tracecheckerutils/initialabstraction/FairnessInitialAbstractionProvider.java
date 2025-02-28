package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.initialabstraction;

import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.fairness.ActionFairnessAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.fairness.GuardedAutomaton2Nwa;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.fairness.GuardedBuchiIntersection;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.reachablestates.NestedWordAutomatonReachableStates;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

public class FairnessInitialAbstractionProvider<L extends IIcfgTransition<?>, A extends INwaOutgoingLetterAndTransitionProvider<L, IPredicate>>
		implements IInitialAbstractionProvider<L, A> {
	private final IInitialAbstractionProvider<L, A> mUnderlying;
	private final IUltimateServiceProvider mServices;

	public FairnessInitialAbstractionProvider(final IInitialAbstractionProvider<L, A> underlying,
			final IUltimateServiceProvider services) {
		mUnderlying = underlying;
		mServices = services;
	}

	@Override
	public A getInitialAbstraction(final IIcfg<? extends IcfgLocation> icfg,
			final Set<? extends IcfgLocation> errorLocs) throws AutomataLibraryException {
		final A underlyingAbstraction = mUnderlying.getInitialAbstraction(icfg, errorLocs);
		final HashRelation<String, L> threads2Actions = new HashRelation<>();
		final Set<L> alphabet = underlyingAbstraction.getAlphabet();
		for (final L letter : alphabet) {
			threads2Actions.addPair(letter.getPrecedingProcedure(), letter);
		}
		final var fairThreadAutomata = threads2Actions.getDomain().stream()
				.map(thread -> new ActionFairnessAutomaton<>(alphabet, threads2Actions.getImage(thread))).toList();
		final var fairAutomaton = new GuardedBuchiIntersection<>(fairThreadAutomata,
				x -> x.stream().flatMap(y -> y.stream()).collect(Collectors.toSet()));
		final var tmp = new NestedWordAutomatonReachableStates<>(new AutomataLibraryServices(mServices),
				new GuardedAutomaton2Nwa<>(fairAutomaton));
		return underlyingAbstraction;
	}
}
