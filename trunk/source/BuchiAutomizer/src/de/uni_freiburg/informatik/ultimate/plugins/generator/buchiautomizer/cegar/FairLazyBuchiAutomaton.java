package de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.cegar;

import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.VpAlphabet;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgForkTransitionThreadOther;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IMLPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.initialabstraction.IInitialAbstractionProvider;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.SleepSetStateFactoryForRefinement.SleepPredicate;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ImmutableSet;

public class FairLazyBuchiAutomaton<L extends IIcfgTransition<?>, IPredicate> implements INwaOutgoingLetterAndTransitionProvider<L, IPredicate>{
	
	private IInitialAbstractionProvider<L, ? extends INwaOutgoingLetterAndTransitionProvider<L, IPredicate>> mInitialAbstractionProvider;
	private INwaOutgoingLetterAndTransitionProvider<L, IPredicate> mInitialAbstraction;
	private Set<IPredicate> mInitialStates;

	public FairLazyBuchiAutomaton(INwaOutgoingLetterAndTransitionProvider<L, IPredicate> initialAbstraction) {
		mInitialAbstraction = initialAbstraction;
		mInitialStates = new HashSet<>();
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
		if (mInitialStates.isEmpty()) {
			for (IPredicate state : mInitialAbstraction.getInitialStates()) {
				mInitialStates.add((IPredicate) getOrConstructPredicate((IMLPredicate) state, ImmutableSet.of(Set.of())));
			}
		}
		return mInitialStates;
	}

	@Override
	public boolean isInitial(IPredicate state) {
		return (mInitialAbstraction.isInitial((IPredicate) ((SleepPredicate<String>) state).getUnderlying()) && isFinal(state));
	}

	@Override
	public boolean isFinal(IPredicate state) {
		return ((SleepPredicate<String>) state).getSleepSet().isEmpty();
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
		Iterable<OutgoingInternalTransition<L, IPredicate>> successors = mInitialAbstraction.internalSuccessors(
				(IPredicate) ((SleepPredicate) state).getUnderlying(), letter);
		Iterator<OutgoingInternalTransition<L, IPredicate>> iterator = successors.iterator();
		ImmutableSet<String> annotations = getEnabledProcedures(state, letter, successors);
		Set<OutgoingInternalTransition<L, IPredicate>> newSuccessors = new HashSet<>();
		while(iterator.hasNext()) {
			IPredicate predicate = (IPredicate) getOrConstructPredicate((IMLPredicate) iterator.next().getSucc(), annotations);
			newSuccessors.add(new OutgoingInternalTransition<>(letter, predicate));
		}
		return newSuccessors;
	}

	private ImmutableSet<String> getEnabledProcedures(IPredicate state, L letter, Iterable<OutgoingInternalTransition<L, IPredicate>> successors) {
		Set<String> annotations = new HashSet<>();
		Set<L> outgoing = mInitialAbstraction.lettersInternal((IPredicate) ((SleepPredicate) state).getUnderlying());
		for (L edge : outgoing) {
			annotations.add(edge.getSucceedingProcedure());
		}
		/*Iterator<OutgoingInternalTransition<L, IPredicate>> iterator = successors.iterator();
		while(iterator.hasNext()) {
			annotations.add(iterator.next().getLetter().getSucceedingProcedure());
		}*/
		if (letter instanceof IIcfgForkTransitionThreadOther) {
			annotations.remove(letter.getSucceedingProcedure());
		}
		annotations.remove(letter.getPrecedingProcedure());
		Set<String> preAnnotations = ((SleepPredicate<String>) state).getSleepSet();
		if (!preAnnotations.isEmpty()) {
			annotations.retainAll(preAnnotations);
		}
		return ImmutableSet.of(annotations);
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
	
	private SleepPredicate<String> getOrConstructPredicate(IMLPredicate state, ImmutableSet<String> annotations) {
		return new SleepPredicate<>(state, annotations);
	}

}
