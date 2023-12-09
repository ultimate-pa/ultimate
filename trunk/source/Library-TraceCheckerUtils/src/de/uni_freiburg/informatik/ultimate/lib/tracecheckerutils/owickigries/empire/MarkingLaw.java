/*
 * Copyright (C) 2023 Matthias Zumkeller
 * Copyright (C) 2023 University of Freiburg
 *
 * This file is part of the ULTIMATE TraceCheckerUtils Library.
 *
 * The ULTIMATE TraceCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TraceCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TraceCheckerUtils Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.owickigries.empire;

import java.util.Collection;
import java.util.HashMap;
import java.util.Map;
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
	public MarkingLaw(final Collection<TerritoryLaw<PLACE>> empireLaw, final BasicPredicateFactory factory) {
		mFactory = factory;
		mMarkingLawMap = getMarkingLaw(empireLaw);
	}

	private HashMap<Marking<PLACE>, IPredicate> getMarkingLaw(final Collection<TerritoryLaw<PLACE>> empireLaw) {
		final HashMap<Marking<PLACE>, IPredicate> markingLaw = new HashMap<>();
		for (final TerritoryLaw<PLACE> territoryLaw : empireLaw) {
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

	public Map<Marking<PLACE>, IPredicate> getLawMap() {
		return mMarkingLawMap;
	}

	public Set<Marking<PLACE>> getMarkings() {
		return mMarkingLawMap.keySet();
	}
}
