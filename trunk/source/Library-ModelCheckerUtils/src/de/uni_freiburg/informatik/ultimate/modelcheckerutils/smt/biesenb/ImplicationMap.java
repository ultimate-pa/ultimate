package de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.biesenb;

import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hoaretriple.IHoareTripleChecker.Validity;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.util.datastructures.poset.IPartialComparator;
import de.uni_freiburg.informatik.ultimate.util.datastructures.poset.IPartialComparator.ComparisonResult;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

public class ImplicationMap<T extends IPredicate> implements IImplicationGraph<T>{

	private final ManagedScript mMgdScript;
	private final BPredicateUnifier mUnifier;
	private final Map<T, Vertex<T>> mVertices;

	protected ImplicationMap(final ManagedScript script, final BPredicateUnifier unifer, T falsePred, T truePred) {
		mMgdScript = script;
		mUnifier = unifer;
		mVertices = new HashMap<>();
		mVertices.put(falsePred, new Vertex<>(falsePred));
		mVertices.put(truePred, new Vertex<>(truePred));
		mVertices.get(falsePred).addDescendant(truePred);
		mVertices.get(truePred).addAncestor(falsePred);
	}
	
	@Override
	public String toString() {
		final StringBuilder bld = new StringBuilder();
		for (final Vertex<T> vertex : mVertices.values()) {
			bld.append("\n " + vertex.toString());
		}
		return bld.toString();
	}

	@Override
	public Validity isCovered(IPredicate lhs, IPredicate rhs) {
		if (getCoveringPredicates(lhs).contains(rhs)) {
			return Validity.VALID;
		}
		return Validity.INVALID;
	}

	@Override
	public Set<IPredicate> getCoveredPredicates(IPredicate pred) {
		Set<T> ancestors = mVertices.get(pred).getAncestors();
		Set<IPredicate> covered = new HashSet<>();
		ancestors.forEach(a -> covered.add(a));
		covered.add(pred);
		return covered;
	}

	@Override
	public Set<IPredicate> getCoveringPredicates(IPredicate pred) {
		Set<T> descendants = mVertices.get(pred).getDescendants();
		Set<IPredicate> covering = new HashSet<>();
		descendants.forEach(d -> covering.add(d));
		covering.add(pred);
		return covering;
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
			if (getCoveringPredicates(o1).contains(o2)) {
				return ComparisonResult.STRICTLY_SMALLER;
			}
			if (getCoveringPredicates(o2).contains(o1)) {
				return ComparisonResult.STRICTLY_GREATER;
			}
			return ComparisonResult.INCOMPARABLE;
		};
	}

	@Override
	public HashRelation<IPredicate, IPredicate> getCopyOfImplicationRelation() {
		throw new UnsupportedOperationException("Not implemented yet");
	}

	@Override
	public boolean unifyPredicate(T predicate) {
		Vertex<T> predVertex = new Vertex<>(predicate);
		final Map<T, Vertex<T>> vDCopy = new HashMap<>(mVertices);
		//find descendants
		while(!vDCopy.isEmpty()) {
			T pivot = chosePivot(vDCopy, true, true);
			Vertex<T> pivotVertex = vDCopy.remove(pivot);
			if(internImplication(predicate, pivot)) {
				predVertex.addDescendant(pivot);
				predVertex.addAllDescendants(pivotVertex.getDescendants());
				pivotVertex.getDescendants().forEach(d -> vDCopy.remove(d));
			} else {
				pivotVertex.getAncestors().forEach(d -> vDCopy.remove(d));
			}
		}
		//find ancestors
		final Map<T, Vertex<T>> vACopy = new HashMap<>(mVertices);
		predVertex.getDescendants().forEach(d -> vACopy.remove(d));
		while(!vACopy.isEmpty()) {
			T pivot = chosePivot(vACopy, true, false);
			Vertex<T> pivotVertex = vACopy.remove(pivot);
			if(internImplication(pivot, predicate)) {
				predVertex.addAncestor(pivot);
				predVertex.addAllAncestors(pivotVertex.getAncestors());
				pivotVertex.getAncestors().forEach(d -> vACopy.remove(d));
			} else {
				pivotVertex.getDescendants().forEach(d -> vACopy.remove(d));
			}
		}
		predVertex.getAncestors().forEach(a -> mVertices.get(a).addDescendant(predicate));
		predVertex.getDescendants().forEach(d -> mVertices.get(d).addAncestor(predicate));
		mVertices.put(predicate, predVertex);
		return true;
	}

	private boolean internImplication(T a, T b) {
		if (a.equals(b)) {
			return true;
		}
		if (mVertices.containsKey(a) && mVertices.containsKey(b)) {
			return getCoveringPredicates(a).contains(b);
		}
		final Term acf = a.getClosedFormula();
		final Term bcf = b.getClosedFormula();
		if (mMgdScript.isLocked()) {
			mMgdScript.requestLockRelease();
		}
		mMgdScript.lock(this);
		final Term imp = mMgdScript.term(this, "and", acf, mMgdScript.term(this, "not", bcf));
		mMgdScript.push(this, 1);
		try {
			mMgdScript.assertTerm(this, imp);
			final Script.LBool result = mMgdScript.checkSat(this);
			if (result == Script.LBool.UNSAT) {
				return true;
			}
			if (result == Script.LBool.SAT) {
				return false;
			}
			throw new UnsupportedOperationException(
					"Cannot handle case were solver cannot decide implication of predicates");
		} finally {
			mMgdScript.pop(this, 1);
			mMgdScript.unlock(this);
		}
	}

	private T chosePivot(Map<T, Vertex<T>> imp, boolean random, boolean first) {
		if(random) {
			return imp.keySet().iterator().next();
		} else {
			int max = 0;
			Vertex<T> pivot = imp.values().iterator().next();
			for (final Vertex<T> v : imp.values()) {
				int a = v.getAncestors().size();
				int b = v.getDescendants().size();
				if(first) b += 1; else a += 1;
				int count = (a * b)/(a + b);
				if(count >= max) {
					max = count;
					pivot = v;
				}
			}
			return pivot.getPredicate();
		}
	}

	@Override
	public Collection<T> removeImpliedVerticesFromCollection(Collection<T> collection) {
		Collection<T> result = new HashSet<>(collection);
		for(T c1 : collection) {
			for(T c2 : collection) {
				if(mVertices.get(c1).getAncestors().contains(c2)) {
					result.remove(c1);
					break;
				}
			}
		}
		return result;
	}

	@Override
	public Collection<T> removeImplyingVerticesFromCollection(Collection<T> collection) {
		Collection<T> result = new HashSet<>(collection);
		for(T c1 : collection) {
			for(T c2 : collection) {
				if(mVertices.get(c1).getDescendants().contains(c2)) {
					result.remove(c1);
					break;
				}
			}
		}
		return result;
	}
	
	private class Vertex<T extends IPredicate> {
		
		private T mPredicate;
		private final Set<T> mDescendants;
		private final Set<T> mAncestors;
		
		private Vertex(final T pred) {
			mPredicate = pred;
			mDescendants = new HashSet<>();
			mAncestors = new HashSet<>();
		}
		
		private T getPredicate() {
			return mPredicate;
		}
		
		private boolean addDescendant(T pred){
			return mDescendants.add(pred);
		}
		
		private boolean addAncestor(T pred){
			return mAncestors.add(pred);
		}
		
		private boolean addAllDescendants(Set<T> preds){
			return mDescendants.addAll(preds);
		}
		
		private boolean addAllAncestors(Set<T> preds){
			return mAncestors.addAll(preds);
		}
		
		private Set<T> getDescendants(){
			return mDescendants;
		}
		
		private Set<T> getAncestors(){
			return mAncestors;
		}
		
		@Override
		public String toString() {
			return mPredicate + "is covered by:" + mDescendants;
		}
	}
}
