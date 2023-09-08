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
import de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.preferences.BuchiAutomizerPreferenceInitializer.FairnessType;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.PredicateFactoryRefinement;

public class FairInitialAbstractionProviderLazy<L extends IIcfgTransition<?>> implements IInitialAbstractionProvider<L,
INwaOutgoingLetterAndTransitionProvider<L, IPredicate>> {

	private IInitialAbstractionProvider<L, ? extends INwaOutgoingLetterAndTransitionProvider<L, IPredicate>> mInitialAbstractionProvider;
	private AutomataLibraryServices mServices;
	private PredicateFactory mPredicateFactory;
	private PredicateFactoryRefinement mStateFactory;
	private FairnessType mFairnessType;

	public FairInitialAbstractionProviderLazy(IIcfg<?> icfg, IInitialAbstractionProvider<L, ? extends INwaOutgoingLetterAndTransitionProvider<L, IPredicate>>
	initialAbstractionProvider, AutomataLibraryServices services, PredicateFactory predicateFactory, PredicateFactoryRefinement stateFactoryForRefinement, FairnessType fairnessType) {
		mInitialAbstractionProvider = initialAbstractionProvider;
		mServices = services;
		mPredicateFactory = predicateFactory;
		mStateFactory = stateFactoryForRefinement;
		mFairnessType = fairnessType;
	}
	
	@Override
	public INwaOutgoingLetterAndTransitionProvider<L, IPredicate> getInitialAbstraction(
			IIcfg<? extends IcfgLocation> icfg, Set<? extends IcfgLocation> errorLocs) throws AutomataLibraryException {
		INwaOutgoingLetterAndTransitionProvider<L, IPredicate> initialAbstraction = mInitialAbstractionProvider.getInitialAbstraction(icfg, errorLocs);
		INwaOutgoingLetterAndTransitionProvider<L, IPredicate> fairAbstraction;
		if (mFairnessType.equals(FairnessType.FAIRNESS_INTERSECTION)) {
			fairAbstraction = (new FairBuchiAutomatonLazyIntersections<L>(icfg, initialAbstraction.getVpAlphabet(), mServices, mPredicateFactory, mStateFactory)).getFairIntersectionAutomaton();
		} else {
			fairAbstraction = new FairBuchiAutomatonLazy<>(icfg, initialAbstraction, new EnabledProceduresAlwaysEnabled<>());
			fairAbstraction = new BuchiIntersectNwa<>(initialAbstraction, fairAbstraction, mStateFactory);
		}		
		/*
		NestedWordAutomatonReachableStates<L, IPredicate> debug = new NestedWordAutomatonReachableStates<>(mServices, fairAbstraction);
		String debugString = debug.toString();
		NestedWordAutomatonReachableStates<L, IPredicate> debugi = new NestedWordAutomatonReachableStates<>(mServices, initialAbstraction);
		String debugiString = debugi.toString();*/
		return fairAbstraction;
	}

}
