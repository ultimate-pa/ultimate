package de.uni_freiburg.informatik.ultimate.lib.smtlibutils.egraph;

import java.util.ArrayList;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;

import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.binaryrelation.BinaryEqualityRelation;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.binaryrelation.RelationSymbol;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ImmutableSet;
import de.uni_freiburg.informatik.ultimate.util.datastructures.UnionFind;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

public class EGraph {
	private final IUltimateServiceProvider mServices;
	private final ManagedScript mMgdScript;
	/**
	 * Internal Union find data structure to partition terms into equivalence classes
	 **/
	private final UnionFind<Term> mUnionFind;

	private final ArrayList<ApplicationTerm> mSelectTerms;
	private final HashMap<ImmutableSet<Term>, HashSet<Term>> mDistinctSets;

	/**
	 * Constructs a new empty e graph
	 **/
	public EGraph(final ManagedScript mgdScript, final IUltimateServiceProvider services) {
		mUnionFind = new UnionFind<>();
		mSelectTerms = new ArrayList<>();
		mDistinctSets = new HashMap<>();

		mMgdScript = mgdScript;
		mServices = services;

	}

	private void addTerm(final Term term) {
		if ((term instanceof ConstantTerm)) {
			mUnionFind.findAndConstructEquivalenceClassIfNeeded(term); // we add terms that do not appear on either side
																		// of an equality/disequality relation so that
																		// we do not need to check for deep equality
																		// later on
		} else if (term instanceof ApplicationTerm) {
			final ApplicationTerm appTerm = (ApplicationTerm) term;
			if (appTerm.getFunction().getName().equals("select")) {
				mSelectTerms.add(appTerm);
			}
			final Term representative = mUnionFind.find(appTerm);
			if (representative == null) {
				mUnionFind.makeEquivalenceClass(appTerm);
				for (final Term arg : appTerm.getParameters()) {
					addTerm(arg);
				}
			}
		} else {
			throw new UnsupportedOperationException("Unsupported term type");
		}

	}

	public void addFormula(final Term formula) {
		final Term[] conjuncts = SmtUtils.getConjuncts(formula);

		for (final Term term : conjuncts) {
			final BinaryEqualityRelation binaryEqRelation = BinaryEqualityRelation.convert(term);
			if (binaryEqRelation == null) {
				addTerm(term); //
			} else {
				final Term lhs = binaryEqRelation.getLhs();
				final Term rhs = binaryEqRelation.getRhs();

				addTerm(lhs);
				addTerm(rhs);

				if (binaryEqRelation.getRelationSymbol() == RelationSymbol.DISTINCT) {
					final ImmutableSet<Term> leftEset = mUnionFind.getContainingSet(lhs);
					final ImmutableSet<Term> rightEset = mUnionFind.getContainingSet(rhs);
					if (!(mDistinctSets.containsKey(leftEset))) {
						mDistinctSets.put(leftEset, new HashSet<>(rightEset));

					} else {
						mDistinctSets.get(leftEset).addAll(rightEset);
					}
					if (!(mDistinctSets.containsKey(rightEset))) {
						mDistinctSets.put(rightEset, new HashSet<>(leftEset));

					} else {
						mDistinctSets.get(rightEset).addAll(leftEset);
					}

				} else if (binaryEqRelation.getRelationSymbol() == RelationSymbol.EQ) {
					union(binaryEqRelation.getLhs(), binaryEqRelation.getRhs());
				} else {
					throw new AssertionError("unexpected relation symbol " + binaryEqRelation.getRelationSymbol());
				}
			}
		}
		postProcessSelects();
	}

	private void union(final Term a, final Term b) {
		final ImmutableSet<Term> A = mUnionFind.getContainingSet(a);
		final ImmutableSet<Term> B = mUnionFind.getContainingSet(b);

		final boolean unioned = mUnionFind.union(a, b);
		if (unioned) {
			final ImmutableSet<Term> E = mUnionFind.getContainingSet(a);
			final HashSet<Term> newDistinct = mDistinctSets.getOrDefault(A, new HashSet<>());
			newDistinct.addAll(mDistinctSets.getOrDefault(B, new HashSet<>()));
			mDistinctSets.remove(A);
			mDistinctSets.remove(B);
			mDistinctSets.put(E, newDistinct);
		}
	}

	private Deque<Pair<ApplicationTerm, ApplicationTerm>> getPossiblyUnionableSelectPairs() {
		final Deque<Pair<ApplicationTerm, ApplicationTerm>> pairs = new LinkedList<>();
		for (int i = 0; i < mSelectTerms.size() - 1; i++) {
			for (int j = i + 1; j < mSelectTerms.size(); j++) {
				final ApplicationTerm select1 = mSelectTerms.get(i);
				final ApplicationTerm select2 = mSelectTerms.get(j);
				if ((!areEquivalent(select1, select2))) {
					pairs.add(new Pair<>(select1, select2));
				}
			}
		}
		return pairs;
	}

	public boolean areEquivalent(final Term a, final Term b) {
		if (mUnionFind.find(a) == null) {
			return false;
		}
		return mUnionFind.getContainingSet(a).equals(mUnionFind.getContainingSet(b));
	}

	public boolean areDistinct(final Term a, final Term b) {
		if (!(mDistinctSets.containsKey(mUnionFind.getContainingSet(a)))
				|| !(mDistinctSets.containsKey(mUnionFind.getContainingSet(b)))) {
			return false;
		}
		return mDistinctSets.get(mUnionFind.getContainingSet(a)).contains(b)
				|| mDistinctSets.get(mUnionFind.getContainingSet(b)).contains(a);

	}

	private void postProcessSelects() {
		final Deque<Pair<ApplicationTerm, ApplicationTerm>> worklist = getPossiblyUnionableSelectPairs();
		while (!(worklist.isEmpty())) {
			final Pair<ApplicationTerm, ApplicationTerm> candidate = worklist.pop();
			final ApplicationTerm select1 = candidate.getFirst();
			final ApplicationTerm select2 = candidate.getSecond();
			if (areEquivalent(select1, select2)) { // we check this to prevent more term pairs from getting added to the
													// worklist
				continue;
			}
			if (areEquivalent(select1.getParameters()[0], select2.getParameters()[0])
					&& areEquivalent(select1.getParameters()[1], select2.getParameters()[1])) {
				union(select1, select2);
				worklist.addAll(getPossiblyUnionableSelectPairs());
			}

		}
	}

	public enum Relation {
		EQUAL, DISTINCT, UNKNOWN
	}

	public Relation getRelation(final Term a, final Term b) {

		if (areEquivalent(a, b)) {
			return Relation.EQUAL;
		} else if (areDistinct(a, b)) {
			return Relation.DISTINCT;
		} else {
			return Relation.UNKNOWN;
		}
	}

}
