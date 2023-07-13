package de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.cegar;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.VpAlphabet;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IMLPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.MLPredicate;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.initialabstraction.IInitialAbstractionProvider;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.SleepSetStateFactoryForRefinement.SleepPredicate;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ImmutableSet;

public class FairLazyBuchiAutomaton<L extends IIcfgTransition<?>, IPredicate> implements INwaOutgoingLetterAndTransitionProvider<L, IPredicate>{
	
	private IInitialAbstractionProvider<L, ? extends INwaOutgoingLetterAndTransitionProvider<L, IPredicate>> mInitialAbstractionProvider;
	private INwaOutgoingLetterAndTransitionProvider<L, IPredicate> mInitialAbstraction;
	private Map<IPredicate, SleepPredicate<String>> mPredicateToAnnotatedPredicate;
	private Map<SleepPredicate<String>, IPredicate> mAnnotatedPredicateToPredicate;
	private Set<IPredicate> mInitialStates;

	public FairLazyBuchiAutomaton(INwaOutgoingLetterAndTransitionProvider<L, IPredicate> initialAbstraction) {
		mInitialAbstraction = initialAbstraction;
		mPredicateToAnnotatedPredicate = new HashMap<>();
		mAnnotatedPredicateToPredicate = new HashMap<>();
	}

	@Override
	public IStateFactory<IPredicate> getStateFactory() {
		// TODO Auto-generated method stub
		return mInitialAbstraction.getStateFactory();
	}

	@Override
	public VpAlphabet<L> getVpAlphabet() {
		// TODO Auto-generated method stub
		return mInitialAbstraction.getVpAlphabet();
	}

	@Override
	public IPredicate getEmptyStackState() {
		// TODO Auto-generated method stub
		return mInitialAbstraction.getEmptyStackState();
	}

	@Override
	public Iterable<IPredicate> getInitialStates() {
		// TODO Auto-generated method stub
		if (mInitialStates.isEmpty()) {
			for (IPredicate state : mInitialAbstraction.getInitialStates()) {
				mInitialStates.add(getOrConstructPredicate((IMLPredicate) state, ImmutableSet.of(Set.of())));
			}
		}
		Iterable<IPredicate> iterable = mInitialStates;
		return iterable;
	}

	@Override
	public boolean isInitial(IPredicate state) {
		// TODO Auto-generated method stub
		return (mInitialAbstraction.isInitial((IPredicate) mPredicateToAnnotatedPredicate.get(state).getUnderlying()) && isFinal(state));
	}

	@Override
	public boolean isFinal(IPredicate state) {
		// TODO Auto-generated method stub
		return mPredicateToAnnotatedPredicate.get(state).getSleepSet().isEmpty();
		//return ((SleepPredicate<String>) state).getSleepSet().isEmpty();
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
		ImmutableSet<String> annotations = getEnabledProcedures(state, letter);
		Iterable<OutgoingInternalTransition<L, IPredicate>> successors = mInitialAbstraction.internalSuccessors(state, letter);
		Set<OutgoingInternalTransition<L, IPredicate>> newSuccessors = new HashSet<>();
		for (OutgoingInternalTransition<L, IPredicate> suc : successors) {
			IPredicate predicate = getOrConstructPredicate((IMLPredicate) suc.getSucc(), annotations);
			newSuccessors.add(new OutgoingInternalTransition<>(letter, predicate));
		}
		Iterable<OutgoingInternalTransition<L, IPredicate>> iterable = newSuccessors;
		return iterable;
	}

	private ImmutableSet<String> getEnabledProcedures(IPredicate state, L letter) {
		Set<String> procedures = new HashSet<>();
		List<IcfgLocation> successors = letter.getSource().getOutgoingNodes();
		for(IcfgLocation loc : successors) {
			procedures.add(loc.getProcedure());
		}
		procedures.remove(letter.getPrecedingProcedure());
		return ImmutableSet.of(procedures);
	}

	@Override
	public Iterable<OutgoingCallTransition<L, IPredicate>> callSuccessors(IPredicate state, L letter) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Iterable<OutgoingReturnTransition<L, IPredicate>> returnSuccessors(IPredicate state, IPredicate hier,
			L letter) {
		// TODO Auto-generated method stub
		return null;
	}
	
	private IPredicate getOrConstructPredicate(IMLPredicate state, ImmutableSet<String> annotations) {
		SleepPredicate<String> annotatedPredicate = new SleepPredicate<>(state, annotations);
		IPredicate predicate  = (IPredicate) annotatedPredicate;
		mPredicateToAnnotatedPredicate.putIfAbsent(predicate, annotatedPredicate);
		mAnnotatedPredicateToPredicate.putIfAbsent(annotatedPredicate, predicate);
		return mAnnotatedPredicateToPredicate.get(annotatedPredicate);
	}

}
