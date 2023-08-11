package de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.cegar;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.VpAlphabet;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.BuchiIntersectNwa;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.reachablestates.NestedWordAutomatonReachableStates;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgForkTransitionThreadOther;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.debugidentifiers.StringDebugIdentifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.PredicateFactoryRefinement;

public class FairBuchiAutomatonLazy<L extends IIcfgTransition<?>> {

	private IIcfg<? extends IcfgLocation> mIcfg;
	private INwaOutgoingLetterAndTransitionProvider<L, IPredicate> mBuchiIntersectAutomaton;
	private PredicateFactory mPredicateFactory;
	private String mMainProcedure;
	private VpAlphabet<L> mVpAlphabet;

	public FairBuchiAutomatonLazy(IIcfg<? extends IcfgLocation> icfg,
			VpAlphabet<L> alphabet, AutomataLibraryServices services, PredicateFactory predicateFactory,
			PredicateFactoryRefinement stateFactoryForRefinement) throws AutomataLibraryException {
		mIcfg = icfg;
		mVpAlphabet = alphabet;
		mPredicateFactory = predicateFactory;
		mMainProcedure = mIcfg.getInitialNodes().iterator().next().getProcedure();
		
		Set<String> procedures = new HashSet<>(); 
		for (L edge : alphabet.getInternalAlphabet()) {
			procedures.add(edge.getPrecedingProcedure());
		}
		for (String procedure : procedures) {		
			/*
			NestedWordAutomatonReachableStates<L, IPredicate> debug = new NestedWordAutomatonReachableStates<>(services, entry.getValue());
			String debugString = debug.toString();
			Integer i = 0;
			*/		
			if (mBuchiIntersectAutomaton == null) {
				mBuchiIntersectAutomaton = new FairLazyProcedureBuchiAutomaton(procedure);
			} else {
				mBuchiIntersectAutomaton = new BuchiIntersectNwa<>(mBuchiIntersectAutomaton, new FairLazyProcedureBuchiAutomaton(procedure), stateFactoryForRefinement);
			}
			/*
			NestedWordAutomatonReachableStates<L, IPredicate> debugfair = new NestedWordAutomatonReachableStates<>(services, mBuchiIntersectAutomaton);
			String debugfairString = debugfair.toString();*/
		}

	}
	
	public INwaOutgoingLetterAndTransitionProvider<L, IPredicate> getFairIntersectionAutomaton(){
		return mBuchiIntersectAutomaton;
	}
	
	private class FairLazyProcedureBuchiAutomaton implements INwaOutgoingLetterAndTransitionProvider<L, IPredicate>{
		
		private HashSet<IPredicate> mProcedureInitialStates;
		private HashSet<IPredicate> mProcedureFinalStates;
		private String mProcedure;
		private ArrayList<IPredicate> mStatesThread;

		public FairLazyProcedureBuchiAutomaton(String procedure) {
			mProcedureInitialStates = new HashSet<>();
			mProcedureFinalStates = new HashSet<>();
			mProcedure = procedure;
			mStatesThread = new ArrayList<>(Arrays.asList(null,null,null));
			
		}

		@Override
		public IStateFactory<IPredicate> getStateFactory() {
			// TODO Auto-generated method stub
			return null;
		}

		@Override
		public VpAlphabet<L> getVpAlphabet() {
			return mVpAlphabet;
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
				if (!mProcedure.equals(mMainProcedure) && letter instanceof IIcfgForkTransitionThreadOther && suc.equals(mProcedure)) {
					return getOrConstructTransition(letter, getOrConstructState(1));
				} else {
					return getOrConstructTransition(letter, state);
				}
			} else {
				if (mIcfg.getProcedureExitNodes().get(mProcedure).equals(letter.getTarget())) {
					return getOrConstructTransition(letter, getOrConstructState(0));
				} else if (pre.equals(mProcedure) && suc.equals(mProcedure)) {
					return getOrConstructTransition(letter, getOrConstructState(2));
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
			if(mStatesThread.get(index) == null) {
				
				IcfgLocation[] loc = new IcfgLocation[1];
				loc[0] = new IcfgLocation(new StringDebugIdentifier("s" + index.toString()), mProcedure);
				IPredicate state = mPredicateFactory.newMLDontCarePredicate(loc);
				mStatesThread.set(index, state);
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
