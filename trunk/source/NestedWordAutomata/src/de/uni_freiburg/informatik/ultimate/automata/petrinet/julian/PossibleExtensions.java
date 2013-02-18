package de.uni_freiburg.informatik.ultimate.automata.petrinet.julian;

import java.util.Collection;
import java.util.Comparator;
import java.util.HashMap;
import java.util.Map;
import java.util.PriorityQueue;

import de.uni_freiburg.informatik.ultimate.automata.petrinet.ITransition;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.Place;

public class PossibleExtensions<S, C> implements IPossibleExtensions<S, C> {

	private PriorityQueue<Event<S, C>> m_Pe;
	private BranchingProcess<S, C> m_BranchingProcess;

	public PossibleExtensions(BranchingProcess<S, C> branchingProcess,
			Comparator<Event<S, C>> order) {
		this.m_BranchingProcess = branchingProcess;

		// anonymous implementation of the Order corresponding to McMillans
		// Algorithm

		// TODO find an appropriate initial Capacity
		this.m_Pe = new PriorityQueue<Event<S, C>>(1000, order);
	}

	@Override
	public Event<S, C> remove() {
		return m_Pe.remove();
	}

	@Override
	public void update(Event<S, C> e) {
		Collection<Candidate<S, C>> candidates = computeCandidates(e);
		for (Candidate<S, C> candidate : candidates) {
			evolveCandidate(candidate);
		}
	}


	/**
	 * Evolves a {@code Candidate} for a new possible Event in all possible ways
	 * and, as a side-effect, adds valid extensions (ones whose predecessors are
	 * a co-set) to he possible extension set.
	 * 
	 * @param m_t
	 * @param m_Chosen
	 * @param m_Places
	 */
	private void evolveCandidate(Candidate<S, C> cand) {
		if (cand.m_Places.isEmpty()) {
			m_Pe.add(new Event<S, C>(cand.m_Chosen, cand.m_t));
			return;
		}
		Place<S, C> p = cand.m_Places.remove(cand.m_Places.size() - 1);
		for (Condition<S, C> c : m_BranchingProcess.place2cond(p)) {
			assert cand.m_t.getPredecessors().contains(c.getPlace());
			assert c.getPlace() == p;
			assert !cand.m_Chosen.contains(c);
			if (m_BranchingProcess.isCoset(cand.m_Chosen, c)) {
				cand.m_Chosen.add(c);
				evolveCandidate(cand);
				cand.m_Chosen.remove(cand.m_Chosen.size() - 1);
			}
		}
		cand.m_Places.add(p);
	}

	// private void evolveCandidate(Transition<S, C> t,
	// Set<Condition<S, C>> chosen, Collection<Place<S, C>> places) {

	/**
	 * computes all {@code Candidate}s for possible extensions that are
	 * successors of {@code Event} e
	 */
	private Collection<Candidate<S, C>> computeCandidates(Event<S, C> e) {
		int initCapacity = 2 
				* e.getSuccessorConditions().size()
				* e.getSuccessorConditions().iterator().next()
						.getPlace().getSuccessors().size();
		final Map<ITransition<S, C>, Candidate<S, C>> candidates = 
				new HashMap<ITransition<S, C>, Candidate<S, C>>(initCapacity);
		for (Condition<S, C> c0 : e.getSuccessorConditions()) {
			for (ITransition<S, C> t : c0.getPlace().getSuccessors()) {
				Candidate<S, C> current;
				if (!candidates.containsKey(t)) {
					current = new Candidate<S, C>((Transition<S, C>)t);
					candidates.put(t, current);
				} else {
					current = candidates.get(t);
				}
				current.m_Chosen.add(c0);
				current.m_Places.remove(c0.getPlace());
				assert current.m_Places.size() + current.m_Chosen.size() == t.getPredecessors().size();
			}
		}
		return candidates.values();
	}


	@Override
	public boolean isEmpy() {
		return m_Pe.isEmpty();
	}

	@Override
	public int size() {
		return m_Pe.size();
	}

}
