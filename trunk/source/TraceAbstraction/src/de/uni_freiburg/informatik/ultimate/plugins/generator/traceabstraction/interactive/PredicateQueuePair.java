package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interactive;

import java.util.Deque;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.DoubleDecker;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;

public class PredicateQueuePair {
	public final Deque<DoubleDecker<IPredicate>> mCallQueue;
	public final Deque<DoubleDecker<IPredicate>> mQueue;

	public PredicateQueuePair(Deque<DoubleDecker<IPredicate>> mCallQueue, Deque<DoubleDecker<IPredicate>> mQueue) {
		this.mCallQueue = mCallQueue;
		this.mQueue = mQueue;
	}
}