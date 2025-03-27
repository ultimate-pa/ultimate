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
	private final Set<Region<P>> mRegions;
	private final Set<Pair<Territory<P>, IPredicate>> mUniquePairs;
	private final long mNumberOfTerritories;

	public ComputeAutomataStatistics(
			final NestedWordAutomatonReachableStates<Transition<L, P>, State<L, P>> empireAutomaton) {
		mEmpireAutomaton = empireAutomaton;
		mRegions = mEmpireAutomaton.getStates().stream().flatMap(s -> s.territory().getRegions().stream())
				.collect(Collectors.toSet());
		mUniquePairs = mEmpireAutomaton.getStates().stream().map(s -> new Pair<>(s.territory(), s.law()))
				.collect(Collectors.toSet());
		mNumberOfTerritories = mEmpireAutomaton.getStates().stream().map(State::territory).distinct().count();
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
		return mEmpireAutomaton.getStates().stream()
				.collect(Collectors.summingLong(x -> sizeComputation.size(x.law().getFormula())));
	}

	/**
	 * Get the sum of Law size and Automaton size
	 *
	 * @return Empire automaton size as long
	 */
	public final long getAnnotationSize() {
		return getAutomatonSize() + getLawSize();
	}

	public final long getNumberOfTerritories() {
		return mNumberOfTerritories;
	}
}
