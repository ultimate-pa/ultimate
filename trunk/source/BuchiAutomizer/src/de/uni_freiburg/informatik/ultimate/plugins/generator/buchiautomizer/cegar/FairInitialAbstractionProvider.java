package de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.cegar;

import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.VpAlphabet;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.BuchiIntersectNwa;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.reachablestates.NestedWordAutomatonReachableStates;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgForkTransitionThreadOther;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.initialabstraction.IInitialAbstractionProvider;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.PredicateFactoryRefinement;

public class FairInitialAbstractionProvider<L extends IIcfgTransition<?>> implements IInitialAbstractionProvider<L,
INwaOutgoingLetterAndTransitionProvider<L, IPredicate>> {
	private IInitialAbstractionProvider<L, ? extends INwaOutgoingLetterAndTransitionProvider<L, IPredicate>> mInitialAbstractionProvider;
	private IIcfg<?> mIcfg;
	private AutomataLibraryServices mServices;
	private PredicateFactoryRefinement mStateFactory;
	private Map<String, INwaOutgoingLetterAndTransitionProvider<L, IPredicate>> mFairAutomataMap;
	private BuchiIntersectNwa<L, IPredicate> mBuchiIntersectAutomaton;
	private Set<L> mInitialAbstractionAlphabet;
	private PredicateFactory mPredicateFactory;
	
	public FairInitialAbstractionProvider(IIcfg<?> icfg, IInitialAbstractionProvider<L, ? extends INwaOutgoingLetterAndTransitionProvider<L, IPredicate>>
	initialAbstractionProvider, AutomataLibraryServices services, PredicateFactory predicateFactory, PredicateFactoryRefinement stateFactoryForRefinement) {
		mInitialAbstractionProvider = initialAbstractionProvider;
		mIcfg = icfg;
		mServices = services;
		mPredicateFactory = predicateFactory;
		mStateFactory = stateFactoryForRefinement;
		mFairAutomataMap = new HashMap<>();
	}

	@Override
	public INwaOutgoingLetterAndTransitionProvider<L, IPredicate> getInitialAbstraction(
			IIcfg<? extends IcfgLocation> icfg, Set<? extends IcfgLocation> errorLocs) throws AutomataLibraryException {
		INwaOutgoingLetterAndTransitionProvider<L, IPredicate> initialAbstraction = mInitialAbstractionProvider.getInitialAbstraction(icfg, errorLocs);
		
		NestedWordAutomatonReachableStates<L, IPredicate> debugi = new NestedWordAutomatonReachableStates<>(mServices, initialAbstraction);
		String debugiString = debugi.toString();
		Integer j = 0;
		
		mInitialAbstractionAlphabet = initialAbstraction.getVpAlphabet().getInternalAlphabet();
		Set<String> procedures = new HashSet<>();
		for (L edge : mInitialAbstractionAlphabet) {
			if (mIcfg.getInitialNodes().contains(edge.getSource())) {
				mFairAutomataMap.computeIfAbsent(edge.getPrecedingProcedure(), v -> getFairAutomatonMainThread(initialAbstraction, edge.getPrecedingProcedure()));
			} else {
				procedures.add(edge.getPrecedingProcedure());
			}
		}
		for (String procedure : procedures) {
			mFairAutomataMap.computeIfAbsent(procedure, v -> getFairAutomaton(initialAbstraction, procedure));
		}
		
		//compute the fair intersections
		for (Entry<String, INwaOutgoingLetterAndTransitionProvider<L, IPredicate>> entry : mFairAutomataMap.entrySet()) {
			NestedWordAutomatonReachableStates<L, IPredicate> debugp = new NestedWordAutomatonReachableStates<>(mServices, entry.getValue());
			String debugpString = debugp.toString();
			if (mBuchiIntersectAutomaton == null) {
				mBuchiIntersectAutomaton = new BuchiIntersectNwa<>(initialAbstraction, entry.getValue(), mStateFactory);
				
				NestedWordAutomatonReachableStates<L, IPredicate> debug = new NestedWordAutomatonReachableStates<>(mServices, mBuchiIntersectAutomaton);
				String debugString = debug.toString();
				Integer i = 0;
				
			} else {
				mBuchiIntersectAutomaton = new BuchiIntersectNwa<>(mBuchiIntersectAutomaton, entry.getValue(), mStateFactory);
				
				NestedWordAutomatonReachableStates<L, IPredicate> debug = new NestedWordAutomatonReachableStates<>(mServices, mBuchiIntersectAutomaton);
				String debugString = debug.toString();
				Integer i = 0;
				
			}
		}
		
		
		NestedWordAutomatonReachableStates<L, IPredicate> debug = new NestedWordAutomatonReachableStates<>(mServices, mBuchiIntersectAutomaton);
		String debugString = debug.toString();
		Integer i = 0;
		
		return mBuchiIntersectAutomaton;
	}
	
	private NestedWordAutomaton<L, IPredicate> getFairAutomatonMainThread(INwaOutgoingLetterAndTransitionProvider<L, IPredicate> initialAbstraction,
			String procedure) {
		VpAlphabet<L> alphabet = initialAbstraction.getVpAlphabet();
		NestedWordAutomaton<L, IPredicate> fairAutomaton = new NestedWordAutomaton<L, IPredicate>(mServices, alphabet, mStateFactory);

		IPredicate s1 = mPredicateFactory.newDebugPredicate("s1");
		fairAutomaton.addState(false, true, s1);
		IPredicate s2 = mPredicateFactory.newDebugPredicate("s2");
		fairAutomaton.addState(true, false, s2);
		IPredicate s3 = mPredicateFactory.newDebugPredicate("s3");
		fairAutomaton.addState(false, true, s3);
		
		for(L edge : mInitialAbstractionAlphabet) {
			String pre = edge.getPrecedingProcedure();
			String suc = edge.getSucceedingProcedure();
			if (pre.equals(procedure) && suc.equals(procedure)) {
				if (mIcfg.getProcedureExitNodes().get(procedure).equals(edge.getTarget())) {
					fairAutomaton.addInternalTransition(s1, edge, s1);
					fairAutomaton.addInternalTransition(s2, edge, s1);
					fairAutomaton.addInternalTransition(s3, edge, s1);
				} else {
					fairAutomaton.addInternalTransition(s1, edge, s1);
					fairAutomaton.addInternalTransition(s2, edge, s3);
					fairAutomaton.addInternalTransition(s3, edge, s3);
				}
			} else {
				fairAutomaton.addInternalTransition(s1, edge, s1);
				fairAutomaton.addInternalTransition(s2, edge, s2);
				fairAutomaton.addInternalTransition(s3, edge, s2);
			}
		}
		
		return fairAutomaton;
	}

	private NestedWordAutomaton<L, IPredicate> getFairAutomaton(INwaOutgoingLetterAndTransitionProvider<L, IPredicate> initialAbstraction,
			String procedure) {
		VpAlphabet<L> alphabet = initialAbstraction.getVpAlphabet();
		NestedWordAutomaton<L, IPredicate> fairAutomaton = new NestedWordAutomaton<L, IPredicate>(mServices, alphabet, mStateFactory);

		IPredicate s1 = mPredicateFactory.newDebugPredicate("s1");
		fairAutomaton.addState(true, true, s1);
		IPredicate s2 = mPredicateFactory.newDebugPredicate("s2");
		fairAutomaton.addState(false, false, s2);
		IPredicate s3 = mPredicateFactory.newDebugPredicate("s3");
		fairAutomaton.addState(false, true, s3);
		for(L edge : mInitialAbstractionAlphabet) {
			String suc = edge.getSucceedingProcedure();
			if (edge instanceof IIcfgForkTransitionThreadOther && suc.equals(procedure)) {
				fairAutomaton.addInternalTransition(s1, edge, s2);
			} else {
				fairAutomaton.addInternalTransition(s1, edge, s1);
			}
		}
		for(L edge : mInitialAbstractionAlphabet) {
			String pre = edge.getPrecedingProcedure();
			String suc = edge.getSucceedingProcedure();
			if (mIcfg.getProcedureExitNodes().get(procedure).equals(edge.getTarget())) {
				fairAutomaton.addInternalTransition(s2, edge, s1);
				fairAutomaton.addInternalTransition(s3, edge, s1);
			} else if (pre.equals(procedure) && suc.equals(procedure)) {
				fairAutomaton.addInternalTransition(s2, edge, s3);
				fairAutomaton.addInternalTransition(s3, edge, s3);
			} else {
				fairAutomaton.addInternalTransition(s2, edge, s2);
				fairAutomaton.addInternalTransition(s3, edge, s2);
			}
			/*
			if (pre.equals(procedure) && suc.equals(procedure)) {
				if (mIcfg.getProcedureExitNodes().get(procedure).equals(edge.getTarget())) {
					fairAutomaton.addInternalTransition(s2, edge, s1);
					fairAutomaton.addInternalTransition(s3, edge, s1);
				} else {
					fairAutomaton.addInternalTransition(s2, edge, s3);
					fairAutomaton.addInternalTransition(s3, edge, s3);
				}	
			} else {
				fairAutomaton.addInternalTransition(s2, edge, s2);
				fairAutomaton.addInternalTransition(s3, edge, s2);
			}*/
		}
		return fairAutomaton;
	}

}
