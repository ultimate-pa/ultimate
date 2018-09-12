package de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.biesenb;

import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hoaretriple.IHoareTripleChecker.Validity;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicateCoverageChecker;
import de.uni_freiburg.informatik.ultimate.util.datastructures.poset.IPartialComparator;

public class PredicateCoverageChecker implements IPredicateCoverageChecker{

	final ImplicationGraph<IPredicate> mImplicationGraph;
	
	public PredicateCoverageChecker(final ImplicationGraph<IPredicate> implicationGraph) {
		mImplicationGraph = implicationGraph;
	}
	
	@Override
	public Validity isCovered(IPredicate lhs, IPredicate rhs) {
		if(mImplicationGraph.implication(lhs, rhs, false)) {
			return Validity.VALID;
		} else {
			return Validity.INVALID;
		}
	}

	@Override
	public Set<IPredicate> getCoveredPredicates(IPredicate pred) {
		Set<IPredicate> predicates = new HashSet<>();
		Set<ImplicationVertex<IPredicate>> vertices =  mImplicationGraph.getVertex(pred).getAncestors();
		for(ImplicationVertex<IPredicate> v : vertices) {
			predicates.add((IPredicate) v.getPredicate());
		}
		predicates.add(pred);
		return predicates;
	}

	@Override
	public Set<IPredicate> getCoveringPredicates(IPredicate pred) {
		Set<IPredicate> predicates = new HashSet<>();
		Set<ImplicationVertex<IPredicate>> vertices =  mImplicationGraph.getVertex(pred).getDescendants();
		for(ImplicationVertex<IPredicate> v : vertices) {
			predicates.add((IPredicate) v.getPredicate());
		}
		predicates.add(pred);
		return predicates;
	}

	@Override
	public IPartialComparator<IPredicate> getPartialComperator() {
		// TODO Auto-generated method stub
		return null;
	}

}
