package de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.biesenb;

import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hoaretriple.IHoareTripleChecker.Validity;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicateCoverageChecker;
import de.uni_freiburg.informatik.ultimate.util.datastructures.poset.IPartialComparator;
import de.uni_freiburg.informatik.ultimate.util.datastructures.poset.IPartialComparator.ComparisonResult;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

public class PredicateCoverageChecker implements IPredicateCoverageChecker {

	private final ImplicationGraph<IPredicate> mImplicationGraph;
	private final BPredicateUnifier mUnifier;

	public PredicateCoverageChecker(final ImplicationGraph<IPredicate> implicationGraph,
			final BPredicateUnifier unifier) {
		mImplicationGraph = implicationGraph;
		mUnifier = unifier;
	}

	@Override
	public Validity isCovered(final IPredicate lhs, final IPredicate rhs) {
		if (mImplicationGraph.implication(lhs, rhs)) {
			return Validity.VALID;
		}
		return Validity.INVALID;
	}

	@Override
	public Set<IPredicate> getCoveredPredicates(final IPredicate pred) {
		final Set<IPredicate> predicates = new HashSet<>();
		final Set<ImplicationVertex<IPredicate>> vertices = mImplicationGraph.getVertex(pred).getAncestors();
		for (final ImplicationVertex<IPredicate> v : vertices) {
			predicates.add(v.getPredicate());
		}
		predicates.add(pred);
		return predicates;
	}

	@Override
	public Set<IPredicate> getCoveringPredicates(final IPredicate pred) {
		final Set<IPredicate> predicates = new HashSet<>();
		final Set<ImplicationVertex<IPredicate>> vertices = mImplicationGraph.getVertex(pred).getDescendants();
		for (final ImplicationVertex<IPredicate> v : vertices) {
			predicates.add(v.getPredicate());
		}
		predicates.add(pred);
		return predicates;
	}

	@Override
	public IPartialComparator<IPredicate> getPartialComperator() {
		return (o1, o2) -> {
			if (!mUnifier.isRepresentative(o1) || !mUnifier.isRepresentative(o2)) {
				throw new AssertionError("predicates unknown to predicate unifier");
			}
			if (o1.equals(o2)) {
				return ComparisonResult.EQUAL;
			}

			final ImplicationVertex<IPredicate> o1v = mImplicationGraph.getVertex(o1);
			final ImplicationVertex<IPredicate> o2v = mImplicationGraph.getVertex(o2);
			assert o1v != null && o2v != null : "implication graph should prevent access to non-existing vertexes";

			if (o1v.getDescendants().contains(o2v)) {
				return ComparisonResult.STRICTLY_SMALLER;
			}
			if (o2v.getDescendants().contains(o1v)) {
				return ComparisonResult.STRICTLY_GREATER;
			}
			return ComparisonResult.INCOMPARABLE;
		};
	}

	@Override
	public HashRelation<IPredicate, IPredicate> getCopyOfImplicationRelation() {
		throw new UnsupportedOperationException("Not implemented yet");
	}

}