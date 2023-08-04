package de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.cegar;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.VpAlphabet;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.BuchiIntersectNwa;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgForkTransitionThreadOther;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.PredicateFactoryRefinement;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ImmutableSet;

public class FairLazyBuchiAutomatonIntersection<L extends IIcfgTransition<?>, IPredicate> implements INwaOutgoingLetterAndTransitionProvider<L, IPredicate> {

	private IIcfg<?> mIcfg;
	private INwaOutgoingLetterAndTransitionProvider<L, IPredicate> mInitialAbstraction; 
	private BuchiIntersectNwa<L, IPredicate> mBuchiIntersectAutomaton;
	private PredicateFactory mPredicateFactory;
	private Map<String, INwaOutgoingLetterAndTransitionProvider<L, IPredicate>> mFairProcedureAutomataMap;
	private String mMainProcedure;
	private INwaOutgoingLetterAndTransitionProvider<L, IPredicate> mFairMainProcedureAutomaton;

	public FairLazyBuchiAutomatonIntersection(IIcfg<?> icfg, INwaOutgoingLetterAndTransitionProvider<L, IPredicate> initialAbstraction,
			PredicateFactory predicateFactory, PredicateFactoryRefinement stateFactoryForRefinement) {
		mIcfg = icfg;
		mInitialAbstraction = initialAbstraction;
		mPredicateFactory = predicateFactory;
		mFairProcedureAutomataMap = new HashMap<>();
		mMainProcedure = mIcfg.getInitialNodes().iterator().next().getProcedure();
		
		for (String procedure : icfg.getProcedureEntryNodes().keySet()) {
			INwaOutgoingLetterAndTransitionProvider<L, IPredicate> fairAutomaton = new FairLazyProcedureBuchiAutomaton<>(procedure);
			if (procedure.equals(mMainProcedure)) {
				mFairMainProcedureAutomaton = fairAutomaton;
			} else {
				mFairProcedureAutomataMap.putIfAbsent(procedure, fairAutomaton);
			}
		}
		
		for (Entry<String, INwaOutgoingLetterAndTransitionProvider<L, IPredicate>> entry : mFairProcedureAutomataMap.entrySet()) {
			if (mBuchiIntersectAutomaton == null) {
				mBuchiIntersectAutomaton = new BuchiIntersectNwa<>(mFairMainProcedureAutomaton, entry.getValue(), stateFactoryForRefinement);
				/*
				NestedWordAutomatonReachableStates<L, IPredicate> debug = new NestedWordAutomatonReachableStates<>(mServices, mBuchiIntersectAutomaton);
				String debugString = debug.toString();
				Integer i = 0;
				*/
			} else {
				mBuchiIntersectAutomaton = new BuchiIntersectNwa<L, IPredicate>(mBuchiIntersectAutomaton, entry.getValue(), stateFactoryForRefinement);
				/*
				NestedWordAutomatonReachableStates<L, IPredicate> debug = new NestedWordAutomatonReachableStates<>(mServices, mBuchiIntersectAutomaton);
				String debugString = debug.toString();
				Integer i = 0;
				*/
			}
		}
	}
	
	@Override
	public IStateFactory<IPredicate> getStateFactory() {
		return mInitialAbstraction.getStateFactory();
	}

	@Override
	public VpAlphabet<L> getVpAlphabet() {
		return mInitialAbstraction.getVpAlphabet();
	}

	@Override
	public IPredicate getEmptyStackState() {
		return mInitialAbstraction.getEmptyStackState();
	}

	@Override
	public Iterable<IPredicate> getInitialStates() {
		// TODO Auto-generated method stub
		return mBuchiIntersectAutomaton.getInitialStates();
	}

	@Override
	public boolean isInitial(IPredicate state) {
		// TODO Auto-generated method stub
		return mBuchiIntersectAutomaton.isInitial(state);
	}

	@Override
	public boolean isFinal(IPredicate state) {
		// TODO Auto-generated method stub
		return mBuchiIntersectAutomaton.isFinal(state);
	}

	@Override
	public int size() {
		// TODO Auto-generated method stub
		return 0;
	}

	@Override
	public String sizeInformation() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Iterable<OutgoingInternalTransition<L, IPredicate>> internalSuccessors(IPredicate state, L letter) {
		// TODO Auto-generated method stub
		return mBuchiIntersectAutomaton.internalSuccessors(state, letter);
	}

	@Override
	public Iterable<OutgoingCallTransition<L, IPredicate>> callSuccessors(IPredicate state, L letter) {
		return List.of();
	}

	@Override
	public Iterable<OutgoingReturnTransition<L, IPredicate>> returnSuccessors(IPredicate state, IPredicate hier,
			L letter) {
		return List.of();
	}
	
	private class FairLazyProcedureBuchiAutomaton<L extends IIcfgTransition<?>, IPredicate> implements INwaOutgoingLetterAndTransitionProvider<L, IPredicate>{
		
		private HashSet<IPredicate> mProcedureInitialStates;
		private HashSet<IPredicate> mProcedureFinalStates;
		private String mProcedure;
		private ArrayList<IPredicate> mStatesThread;

		public FairLazyProcedureBuchiAutomaton(String procedure) {
			mProcedureInitialStates = new HashSet<>();
			mProcedure = procedure;
			mStatesThread = new ArrayList<IPredicate>();
		}

		@Override
		public IStateFactory<IPredicate> getStateFactory() {
			// TODO Auto-generated method stub
			return null;
		}

		@Override
		public VpAlphabet<L> getVpAlphabet() {
			// TODO Auto-generated method stub
			return null;
		}

		@Override
		public IPredicate getEmptyStackState() {
			// TODO Auto-generated method stub
			return null;
		}

		@Override
		public Iterable<IPredicate> getInitialStates() {
			if (mProcedureInitialStates.isEmpty()) {
				if(mProcedure.equals(mMainProcedure)) {
					getOrConstructState(1);
				} else {
					getOrConstructState(0);
				}
			}
			return mProcedureInitialStates;
		}

		@Override
		public boolean isInitial(IPredicate state) {
			return getInitialStates().iterator().next().equals(state);
		}

		@Override
		public boolean isFinal(IPredicate state) {
			return mProcedureFinalStates.contains(state);
		}

		@Override
		public int size() {
			// TODO Auto-generated method stub
			return 0;
		}

		@Override
		public String sizeInformation() {
			// TODO Auto-generated method stub
			return null;
		}

		@Override
		public Iterable<OutgoingInternalTransition<L, IPredicate>> internalSuccessors(IPredicate state, L letter) {
			String pre = letter.getPrecedingProcedure();
			String suc = letter.getSucceedingProcedure();
			if (state.equals(mStatesThread.get(0))) {
				if (letter instanceof IIcfgForkTransitionThreadOther && suc.equals(mProcedure)) {
					return getOrConstructTransition(letter, getOrConstructState(1));
				} else {
					return getOrConstructTransition(letter, state);
				}
			} else {
				if (pre.equals(mProcedure) && suc.equals(mProcedure)) {
					if (mIcfg.getProcedureExitNodes().get(mProcedure).equals(letter.getTarget())) {
						return getOrConstructTransition(letter, getOrConstructState(0));
					} else {
						return getOrConstructTransition(letter, getOrConstructState(2));
					}	
				} else {
					return getOrConstructTransition(letter, getOrConstructState(1));
				}
			}
		}

		@Override
		public Iterable<OutgoingCallTransition<L, IPredicate>> callSuccessors(IPredicate state, L letter) {
			return List.of();
		}

		@Override
		public Iterable<OutgoingReturnTransition<L, IPredicate>> returnSuccessors(IPredicate state, IPredicate hier,
				L letter) {
			return List.of();
		}
		
		private IPredicate getOrConstructState(Integer index) {
			if(mStatesThread.get(index).equals(null)) {
				IPredicate state = (IPredicate) mPredicateFactory.newDebugPredicate("s"+index);
				mStatesThread.add(index, state);
				if(!index.equals(1)) {
					mProcedureFinalStates.add(state);
				}
				if((mProcedure.equals(mMainProcedure) && index.equals(1)) || (!mProcedure.equals(mMainProcedure) && index.equals(0))) {
					mProcedureInitialStates.add(state);
				} 
			}
			return mStatesThread.get(index);			
		}
		

		private Iterable<OutgoingInternalTransition<L, IPredicate>> getOrConstructTransition(L letter, IPredicate suc) {
			OutgoingInternalTransition<L, IPredicate> transition = new OutgoingInternalTransition<>(letter, suc);
			return Set.of(transition);
		}

	}
}
