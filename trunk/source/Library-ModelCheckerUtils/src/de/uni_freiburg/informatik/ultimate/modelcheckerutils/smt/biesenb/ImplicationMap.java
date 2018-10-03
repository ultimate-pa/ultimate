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
	private final Map<T, Set<T>> mDescendants;
	private final Map<T, Set<T>> mAncestors;
	private final boolean mRandom;

	protected ImplicationMap(final ManagedScript script, final BPredicateUnifier unifer, T falsePred, T truePred, boolean random) {
		mMgdScript = script;
		mUnifier = unifer;
		mDescendants = new HashMap<>();
		mAncestors = new HashMap<>();
		mRandom = random;
		mDescendants.put(falsePred, new HashSet<>());
		mDescendants.put(truePred, new HashSet<>());
		mAncestors.put(falsePred, new HashSet<>());
		mAncestors.put(truePred, new HashSet<>());
		mDescendants.get(falsePred).add(truePred);
		mAncestors.get(truePred).add(falsePred);
	}
	
	protected Map<T, Set<T>> getDescendantsMap(){
		return mDescendants;
	}
	
	protected Map<T, Set<T>> getAncestorsMap(){
		return mAncestors;
	}
	
	@Override
	public String toString() {
		final StringBuilder bld = new StringBuilder();
		for (final T pred : mDescendants.keySet()) {
			bld.append("\n " + pred + "is covered by:" + mDescendants.get(pred));
		}
		return bld.toString();
	}

	@SuppressWarnings("unchecked")
	@Override
	public Validity isCovered(IPredicate lhs, IPredicate rhs) {
		if (getCoveringPredicates(lhs).contains(rhs)) {
			return Validity.VALID;
		}
		return Validity.INVALID;
	}

	@Override
	public Set<IPredicate> getCoveredPredicates(IPredicate pred) {
		Set<T> ancestors = mAncestors.get(pred);
		Set<IPredicate> covered = new HashSet<>(ancestors.size() + 1);
		ancestors.forEach(a -> covered.add(a));
		covered.add(pred);
		return covered;
	}

	@Override
	public Set<IPredicate> getCoveringPredicates(IPredicate pred) {
		Set<T> descendants = mDescendants.get(pred);
		Set<IPredicate> covering = new HashSet<>(descendants.size() + 1);
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
		Map<T, Set<T>> dCopy = new HashMap<>(mDescendants);
		final Set<T> predDescendants = new HashSet<>();
		//find descendants
		while(!dCopy.isEmpty()) {
			T pivot = chosePivot(dCopy.keySet(), true);
			Set<T> pivotDescendants = dCopy.remove(pivot);
			if(internImplication(predicate, pivot)) {
				predDescendants.add(pivot);
				predDescendants.addAll(pivotDescendants);
				pivotDescendants.forEach(d -> dCopy.remove(d));
			} else {
				mAncestors.get(pivot).forEach(a -> dCopy.remove(a));
			}
		}
		//determine possible ancestors
		final Map<T, Set<T>> aCopy = new HashMap<>();
		//option 1
//		int min = mAncestors.size() + 1;
//		T minAncestor = null;
//		for(T d : predDescendants) {
//			if(mAncestors.get(d).size() < min) {
//				min = mAncestors.get(d).size();
//				minAncestor = d;
//			}
//		}
//		mAncestors.get(minAncestor).forEach(a -> aCopy.put(a, mAncestors.get(a)));
		//option 2
		mAncestors.get(predDescendants.iterator().next()).forEach(a -> aCopy.put(a, mAncestors.get(a)));
		for(T d : predDescendants) {
			Set<T> it = new HashSet<T>(aCopy.keySet());
			for(T a : it) {
				if(!mAncestors.get(d).contains(a)) {
					aCopy.remove(a);
				}
			}
		}
		//find ancestors
		final Set<T> predAncestors = new HashSet<>();
		while(!aCopy.isEmpty()) {
			T pivot = chosePivot(aCopy.keySet(), false);
			Set<T> pivotAncestors = aCopy.remove(pivot);
			if(internImplication(pivot, predicate)) {
				predAncestors.add(pivot);
				predAncestors.addAll(pivotAncestors);
				pivotAncestors.forEach(a -> aCopy.remove(a));
			} else {
				mDescendants.get(pivot).forEach(d -> aCopy.remove(d));
			}
		}
		predAncestors.forEach(a -> mDescendants.get(a).add(predicate));
		predDescendants.forEach(d -> mAncestors.get(d).add(predicate));
		mDescendants.put(predicate, predDescendants);
		mAncestors.put(predicate, predAncestors);
		return true;
	}

	private boolean internImplication(T a, T b) {
		if (a.equals(b)) {
			return true;
		}
		if (mDescendants.containsKey(a) && mDescendants.containsKey(b)) {
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

	private T chosePivot(Set<T> set, boolean first) {
		if(mRandom) {
			return set.iterator().next();
		} else {
			int max = 0;
			T pivot = set.iterator().next();
			for (final T pred : set) {
				int a = mAncestors.get(pred).size();
				int b = mDescendants.get(pred).size();
				if(first) b += 1; else a += 1;
				int count = (a * b)/(a + b);
				if(count >= max) {
					max = count;
					pivot = pred;
				}
			}
			return pivot;
		}
	}

	@Override
	public Collection<T> removeImpliedVerticesFromCollection(Collection<T> collection) {
		Collection<T> result = new HashSet<>(collection);
		for(T c1 : collection) {
			for(T c2 : collection) {
				if(mAncestors.get(c1).contains(c2)) {
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
				if(mDescendants.get(c1).contains(c2)) {
					result.remove(c1);
					break;
				}
			}
		}
		return result;
	}
}
