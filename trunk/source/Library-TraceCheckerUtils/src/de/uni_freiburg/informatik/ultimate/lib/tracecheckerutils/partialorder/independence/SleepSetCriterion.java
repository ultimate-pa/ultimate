package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.independence;

import java.util.Random;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.SleepSetStateFactoryForRefinement.SleepPredicate;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ImmutableSet;

public class SleepSetCriterion<L, S> implements IConditionalCommutativityCriterion<L, S> {

	/*
	public SleepSetCriterion() {
	}*/
	
	@Override
	public boolean decide(S state, L letter1, L letter2) {
		if (state instanceof SleepPredicate) {
			ImmutableSet<?> sleepSet = ((SleepPredicate<L>) state).getSleepSet();
			return (sleepSet.contains(letter1) || sleepSet.contains(letter2));
		}
		return false;
	}

	@Override
	public boolean decide(IPredicate condition) {
		return condition != null;
	}

}
