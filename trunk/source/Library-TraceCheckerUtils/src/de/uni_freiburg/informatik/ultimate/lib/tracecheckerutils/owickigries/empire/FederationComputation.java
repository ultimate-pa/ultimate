package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.owickigries.empire;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Function;

import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNetSuccessorProvider;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.BasicPredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.owickigries.crown.CrownsEmpire;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.owickigries.crown.PlacesCoRelation;
import de.uni_freiburg.informatik.ultimate.util.statistics.IStatisticsDataProvider;

public class FederationComputation<L, P> {
	Federation<P> mFederation;
	private final Map<IPredicate, P> mPredicatePlaceMap = new HashMap<>();

	public FederationComputation(final IUltimateServiceProvider services, final BasicPredicateFactory predicateFactory,
			final IPetriNetSuccessorProvider<L, P> refinedNet, final Set<P> originalPlaces,
			final List<Set<P>> proofPlaces, final PlacesCoRelation<P> coRelation,
			final Function<P, IPredicate> assertionPlace2Predicate) {
		final var proofEmpireMap = new HashMap<Set<P>, EmpireAnnotation<P>>();
		for (final Set<P> set : proofPlaces) {
			final List<Set<P>> proofSet = new ArrayList<>();
			proofSet.add(set);
			final var empireComputation = new EmpireComputation<>(services, predicateFactory, refinedNet,
					originalPlaces, proofSet, coRelation, assertionPlace2Predicate);
			proofEmpireMap.put(set, empireComputation.getEmpire());
			mPredicatePlaceMap.putAll(empireComputation.getPredicatePlaceMap());
		}
		mFederation = new Federation<>(proofEmpireMap);
	}

	public Federation<P> getFederation() {
		return mFederation;
	}

	public Map<IPredicate, P> getPredicatePlaceMap() {
		return mPredicatePlaceMap;
	}

	public IStatisticsDataProvider getStatistics() {
		final var statistics = new CrownsEmpire.Statistics();
		statistics.reportEmpire(mFederation.getUnitedEmpire());
		return statistics;
	}
}
