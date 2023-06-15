/*
 * Copyright (C) 2022 Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 * Copyright (C) 2022 University of Freiburg
 *
 * This file is part of the ULTIMATE Automata Library.
 *
 * The ULTIMATE Automata Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Automata Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Automata Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Automata Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Automata Library grant you additional permission
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.cegar;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.petrinet.Marking;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.ISLPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap2;

/**
 * Converts a Marking (that represents the locations) into one single IPredicate. Uses caching to avoid multiple
 * predicates for the same locations.
 *
 * @author Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 *
 */
public class Marking2MLPredicate {
	private final PredicateFactory mPredicateFactory;
	private final NestedMap2<Set<IcfgLocation>, Term, IPredicate> mCache;

	public Marking2MLPredicate(final PredicateFactory predicateFactory) {
		mPredicateFactory = predicateFactory;
		mCache = new NestedMap2<>();
	}

	public IPredicate markingToPredicate(final Marking<IPredicate> marking) {
		final Set<IcfgLocation> locations = new HashSet<>();
		final ArrayList<Term> terms = new ArrayList<>();
		for (final IPredicate p : marking) {
			if (p instanceof ISLPredicate) {
				final IcfgLocation loc = ((ISLPredicate) p).getProgramPoint();
				// TODO: This is quite hacky to exclude null...
				if (loc != null) {
					locations.add(loc);
					terms.add(p.getFormula());
				}
			}
		}
		final Term conjunction = mPredicateFactory.andT(terms).getFormula();
		IPredicate result = mCache.get(locations, conjunction);
		if (result == null) {
			result = mPredicateFactory.newMLPredicate(locations.toArray(IcfgLocation[]::new), conjunction);
			mCache.put(locations, conjunction, result);
		}
		return result;
	}
}
