package de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.cegar;

import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.BuchiIntersectNwa;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.reachablestates.NestedWordAutomatonReachableStates;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.initialabstraction.IInitialAbstractionProvider;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.PredicateFactoryRefinement;

public class FairInitialAbstractionProviderLazy<L extends IIcfgTransition<?>> implements IInitialAbstractionProvider<L,
INwaOutgoingLetterAndTransitionProvider<L, IPredicate>> {

	private IInitialAbstractionProvider<L, ? extends INwaOutgoingLetterAndTransitionProvider<L, IPredicate>> mInitialAbstractionProvider;
	private AutomataLibraryServices mServices;
	private PredicateFactory mPredicateFactory;
	private PredicateFactoryRefinement mStateFactory;

	public FairInitialAbstractionProviderLazy(IIcfg<?> icfg, IInitialAbstractionProvider<L, ? extends INwaOutgoingLetterAndTransitionProvider<L, IPredicate>>
	initialAbstractionProvider, AutomataLibraryServices services, PredicateFactory predicateFactory, PredicateFactoryRefinement stateFactoryForRefinement) {
		mInitialAbstractionProvider = initialAbstractionProvider;
		mServices = services;
		mPredicateFactory = predicateFactory;
		mStateFactory = stateFactoryForRefinement;
	}
	
	@Override
	public INwaOutgoingLetterAndTransitionProvider<L, IPredicate> getInitialAbstraction(
			IIcfg<? extends IcfgLocation> icfg, Set<? extends IcfgLocation> errorLocs) throws AutomataLibraryException {
		// TODO Auto-generated method stub
		INwaOutgoingLetterAndTransitionProvider<L, IPredicate> initialAbstraction = mInitialAbstractionProvider.getInitialAbstraction(icfg, errorLocs);
		//FairLazyBuchiAutomaton<L> fairAbstraction = new FairLazyBuchiAutomaton<>(icfg, initialAbstraction, new EnabledProceduresWeakFairness<>());
		INwaOutgoingLetterAndTransitionProvider<L, IPredicate> fairAbstraction = (new FairLazyBuchiAutomatonIntersection<L>(icfg, initialAbstraction, mServices, mPredicateFactory, mStateFactory)).getFairIntersectionAutomaton();
		//fairAbstraction = new BuchiIntersectNwa<>(initialAbstraction, fairAbstraction, mStateFactory);
		NestedWordAutomatonReachableStates<L, IPredicate> debug = new NestedWordAutomatonReachableStates<>(mServices, fairAbstraction);
		String debugString = debug.toString();
		NestedWordAutomatonReachableStates<L, IPredicate> debugi = new NestedWordAutomatonReachableStates<>(mServices, initialAbstraction);
		String debugiString = debugi.toString();
		return fairAbstraction;
	}

}
