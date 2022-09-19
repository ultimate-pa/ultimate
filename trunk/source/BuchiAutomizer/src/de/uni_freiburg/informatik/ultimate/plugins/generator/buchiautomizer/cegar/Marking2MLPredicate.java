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
