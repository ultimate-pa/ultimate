package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.owickigries.empire;

import java.util.Collection;
import java.util.HashMap;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.petrinet.Marking;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.BasicPredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;

/**
 * Class represents the mapping between a Marking and its corresponding Law wrt. to a specific Empire annotation.
 *
 * @author Matthias Zumkeller (zumkellm@informatik.uni-freiburg.de)
 *
 * @param <PLACE>
 *            The type of places in the Petri program
 * @param <LETTER>
 *            The type of statements in the Petri program
 */
public class MarkingLaw<PLACE, LETTER> {
	private final HashMap<Marking<PLACE>, IPredicate> mMarkingLawMap;
	private final BasicPredicateFactory mFactory;

	/**
	 * Construct a map between all Territories and their Laws.
	 *
	 * @param empireLaw
	 *            Set of TerritoryLaw for each Territory of an Empire
	 * @param factory
	 *            Factory for IPredicate operations
	 */
	public MarkingLaw(final Collection<TerritoryLaw<PLACE, LETTER>> empireLaw, final BasicPredicateFactory factory) {
		mFactory = factory;
		mMarkingLawMap = getMarkingLaw(empireLaw);
	}

	private HashMap<Marking<PLACE>, IPredicate> getMarkingLaw(final Collection<TerritoryLaw<PLACE, LETTER>> empireLaw) {
		final HashMap<Marking<PLACE>, IPredicate> markingLaw = new HashMap<>();
		for (final TerritoryLaw<PLACE, LETTER> territoryLaw : empireLaw) {
			final Set<Marking<PLACE>> treaty = territoryLaw.getTerritory().getTreaty();
			for (final Marking<PLACE> marking : treaty) {
				markingLaw.merge(marking, territoryLaw.getLaw(), (p1, p2) -> mFactory.and(p1, p2));
			}
		}
		return markingLaw;
	}

	/**
	 * Get Law corresponding to markings wrt. the Empire for which MarkingLaw was instantiated.
	 *
	 * @param marking
	 *            Marking to be mapped to its Law
	 * @return Law of the marking if it exists, null else.
	 */
	public IPredicate getMarkingLaw(final Marking<PLACE> marking) {
		return mMarkingLawMap.get(marking);
	}

	public Set<Marking<PLACE>> getMarkings() {
		return mMarkingLawMap.keySet();
	}
}
