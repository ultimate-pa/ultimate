package de.uni_freiburg.informatik.ultimate.lib.proofs.owickigries.empire;

import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.reachablestates.NestedWordAutomatonReachableStates;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.Transition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.proofs.owickigries.empire.EmpireAutomaton.State;
import de.uni_freiburg.informatik.ultimate.smtinterpol.util.DAGSize;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

public class ComputeAutomataStatistics<L, P> {
	private final NestedWordAutomatonReachableStates<Transition<L, P>, State<L, P>> mEmpireAutomaton;
	Set<Region<P>> mRegions;
	Set<Pair<Territory<P>, IPredicate>> mUniquePairs;

	public ComputeAutomataStatistics(
			final NestedWordAutomatonReachableStates<Transition<L, P>, State<L, P>> empireAutomaton) {
		mEmpireAutomaton = empireAutomaton;
		mRegions = mEmpireAutomaton.getStates().stream().flatMap(s -> s.territory().getRegions().stream())
				.collect(Collectors.toSet());
		mUniquePairs = mEmpireAutomaton.getStates().stream().map(s -> new Pair<>(s.territory(), s.law()))
				.collect(Collectors.toSet());
	}

	/**
	 * Get the number of regions in the states of the automaton
	 *
	 * @return Number of regions
	 */
	public int getRegionCount() {
		return mRegions.size();
	}

	/**
	 *
	 * @return Number of (reachable) states in the automaton
	 */
	public int getAutomatonSize() {
		return mEmpireAutomaton.getStates().size();
	}

	/**
	 * The number of unique (territory, law) pairs in the automaton
	 *
	 * @return Number of (territory, law) pairs
	 */
	public int getUniquePairsSize() {
		return mUniquePairs.size();
	}

	/**
	 * Get the size of the Law i.e. sum of all formulae.
	 *
	 * @return Size of the law as long.
	 */
	public final long getLawSize() {
		final DAGSize sizeComputation = new DAGSize();
		return mUniquePairs.stream()
				.collect(Collectors.summingLong(x -> sizeComputation.size(x.getSecond().getFormula())));
	}

	/**
	 * Get the sum of Law size and Automaton size
	 *
	 * @return Empire automaton size as long
	 */
	public final long getAnnotationSize() {
		return getAutomatonSize() + getLawSize();
	}
}
