package de.uni_freiburg.informatik.ultimate.lib.smtlibutils.egraph;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.binaryrelation.BinaryEqualityRelation;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.binaryrelation.RelationSymbol;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.util.datastructures.CrossProducts;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;
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

	private final HashMap<ImmutableSet<Term>, Set<ApplicationTerm>> mSelectArrayPartition;
	private final HashMap<ImmutableSet<Term>, Set<ApplicationTerm>> mSelectIndexPartition;

	/**
	 * Constructs a new empty e graph
	 **/
	public EGraph(final ManagedScript mgdScript, final IUltimateServiceProvider services) {
		mUnionFind = new UnionFind<>();
		mSelectTerms = new ArrayList<>();
		mDistinctSets = new HashMap<>();
		mSelectArrayPartition = new HashMap<>();
		mSelectIndexPartition = new HashMap<>();

		mMgdScript = mgdScript;
		mServices = services;

	}

	// assumes select term arguments have already been added
	private void addSelectTerm(final ApplicationTerm selectTerm) {
		assert selectTerm.getFunction().getName().equals("select");
		assert selectTerm.getParameters().length == 2;
		final Term array = selectTerm.getParameters()[0];
		final Term index = selectTerm.getParameters()[1];

		ImmutableSet<Term> arrayESet = mUnionFind.getContainingSet(array);
		ImmutableSet<Term> indexESet = mUnionFind.getContainingSet(index);

		final Set<ApplicationTerm> alreadyEquivalentSelects =
				DataStructureUtils.intersection(mSelectArrayPartition.getOrDefault(arrayESet, new HashSet<>()),
						mSelectIndexPartition.getOrDefault(indexESet, new HashSet<>()));
		// TODO: prove we don't need fixed point here
		for (final ApplicationTerm alreadyEquiv : alreadyEquivalentSelects) {
			union(selectTerm, alreadyEquiv);
		}
		arrayESet = mUnionFind.getContainingSet(array);
		indexESet = mUnionFind.getContainingSet(index);

		if (mSelectArrayPartition.containsKey(arrayESet)) {
			mSelectArrayPartition.get(arrayESet).add(selectTerm);
		} else {
			final HashSet<ApplicationTerm> newSelectSet = new HashSet<>();
			newSelectSet.add(selectTerm);
			mSelectArrayPartition.put(arrayESet, newSelectSet);
		}

		if (mSelectIndexPartition.containsKey(indexESet)) {
			mSelectIndexPartition.get(indexESet).add(selectTerm);
		} else {
			final HashSet<ApplicationTerm> newSelectSet = new HashSet<>();
			newSelectSet.add(selectTerm);
			mSelectIndexPartition.put(indexESet, newSelectSet);
		}

	}

	private void addTerm(final Term term) {
		if ((term instanceof ConstantTerm)) {
			mUnionFind.findAndConstructEquivalenceClassIfNeeded(term); // we add terms that do not appear on either side
																		// of an equality/disequality relation so that
																		// we do not need to check for deep equality
																		// later on
		} else if (term instanceof ApplicationTerm) {
			final ApplicationTerm appTerm = (ApplicationTerm) term;

			final Term representative = mUnionFind.find(appTerm);
			if (representative == null) {
				mUnionFind.makeEquivalenceClass(appTerm);
				for (final Term arg : appTerm.getParameters()) {
					addTerm(arg);
				}
			}
			if (appTerm.getFunction().getName().equals("select")) {
				addSelectTerm(appTerm);
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
					unionWithImplied(binaryEqRelation.getLhs(), binaryEqRelation.getRhs());
				} else {
					throw new AssertionError("unexpected relation symbol " + binaryEqRelation.getRelationSymbol());
				}
			}
		}
	}

	private static class UnionOperation {
		public ImmutableSet<Term> A;
		public ImmutableSet<Term> B;
		public ImmutableSet<Term> E;

		public UnionOperation(final ImmutableSet<Term> A, final ImmutableSet<Term> B, final ImmutableSet<Term> E) {
			this.A = A;
			this.B = B;
			this.E = E;
		}
	}

	private void findImpliedSelectUnions(final ImmutableSet<Term> A, final ImmutableSet<Term> B,
			final ImmutableSet<Term> E) {

		final List<Pair<Set<ApplicationTerm>, Set<ApplicationTerm>>> pairsToBeUnioned = new ArrayList<>();
		// find set of pairs that we should union because their indexes are now the same
		for (final ImmutableSet<Term> arrayPartition : mSelectArrayPartition.keySet()) {
			final Set<ApplicationTerm> aB1 = DataStructureUtils.intersection(mSelectArrayPartition.get(arrayPartition),
					mSelectIndexPartition.getOrDefault(A, new HashSet<>()));
			final Set<ApplicationTerm> aB2 = DataStructureUtils.intersection(mSelectArrayPartition.get(arrayPartition),
					mSelectIndexPartition.getOrDefault(B, new HashSet<>()));
			pairsToBeUnioned.add(new Pair<>(aB1, aB2));
		}
		// find set of pairs that we should union because their arrays are now the same
		for (final ImmutableSet<Term> indexPartition : mSelectIndexPartition.keySet()) {
			final Set<ApplicationTerm> bA1 = DataStructureUtils.intersection(mSelectIndexPartition.get(indexPartition),
					mSelectArrayPartition.getOrDefault(A, new HashSet<>()));
			final Set<ApplicationTerm> bA2 = DataStructureUtils.intersection(mSelectIndexPartition.get(indexPartition),
					mSelectArrayPartition.getOrDefault(B, new HashSet<>()));
			pairsToBeUnioned.add(new Pair<>(bA1, bA2));

		}
		// union all the pairs and collect new sets A, B, and E to ensure fixed point
		final List<UnionOperation> unions = new ArrayList<>();
		for (final Pair<Set<ApplicationTerm>, Set<ApplicationTerm>> pairSet : pairsToBeUnioned) {
			for (final List<ApplicationTerm> pair : CrossProducts
					.crossProductOfSets(Arrays.asList(pairSet.getFirst(), pairSet.getSecond()))) {
				final ImmutableSet<Term> APrime = mUnionFind.getContainingSet(pair.get(0));
				final ImmutableSet<Term> BPrime = mUnionFind.getContainingSet(pair.get(1));
				if (union(pair.get(0), pair.get(1))) {
					final ImmutableSet<Term> EPrime = mUnionFind.getContainingSet(pair.get(0));
					unions.add(new UnionOperation(APrime, BPrime, EPrime));
				}
			}
		}

		for (final UnionOperation unionOp : unions) {
			findImpliedSelectUnions(unionOp.A, unionOp.B, unionOp.E);
		}
	}

	private void unionSelectTerms(final ImmutableSet<Term> A, final ImmutableSet<Term> B, final ImmutableSet<Term> E) {
		final Set<ApplicationTerm> newArrayPartionElement =
				DataStructureUtils.union(mSelectArrayPartition.getOrDefault(A, new HashSet<>()),
						mSelectArrayPartition.getOrDefault(B, new HashSet<>()));
		final Set<ApplicationTerm> newIndexPartionElement =
				DataStructureUtils.union(mSelectIndexPartition.getOrDefault(A, new HashSet<>()),
						mSelectIndexPartition.getOrDefault(B, new HashSet<>()));
		mSelectArrayPartition.remove(A);
		mSelectArrayPartition.remove(B);
		mSelectArrayPartition.put(E, newArrayPartionElement);
		mSelectIndexPartition.remove(A);
		mSelectIndexPartition.remove(B);
		mSelectIndexPartition.put(E, newIndexPartionElement);
	}

	private void unionDistinctTerms(final ImmutableSet<Term> A, final ImmutableSet<Term> B,
			final ImmutableSet<Term> E) {
		final HashSet<Term> newDistinct = mDistinctSets.getOrDefault(A, new HashSet<>());
		newDistinct.addAll(mDistinctSets.getOrDefault(B, new HashSet<>()));
		mDistinctSets.remove(A);
		mDistinctSets.remove(B);
		mDistinctSets.put(E, newDistinct);
	}

	private void unionWithImplied(final Term a, final Term b) {
		final ImmutableSet<Term> A = mUnionFind.getContainingSet(a);
		final ImmutableSet<Term> B = mUnionFind.getContainingSet(b);
		final boolean unioned = union(a, b);
		if (unioned) {
			final ImmutableSet<Term> E = mUnionFind.getContainingSet(a);
			findImpliedSelectUnions(A, B, E);
		}
	}

	private boolean union(final Term a, final Term b) {
		final ImmutableSet<Term> A = mUnionFind.getContainingSet(a);
		final ImmutableSet<Term> B = mUnionFind.getContainingSet(b);

		final boolean unioned = mUnionFind.union(a, b);
		if (unioned) {
			final ImmutableSet<Term> E = mUnionFind.getContainingSet(a);
			unionSelectTerms(A, B, E);
			unionDistinctTerms(A, B, E);
		}
		return unioned;
	}

	public enum Implication {
		IMPLIED, UNKNOWN
	}

	public Implication isImplied(final Term term) {
		final BinaryEqualityRelation binaryEqRelation = BinaryEqualityRelation.convert(term);
		if (binaryEqRelation != null) {
			final Term lhs = binaryEqRelation.getLhs();
			final Term rhs = binaryEqRelation.getRhs();

			final RelationSymbol termRelationSymbol = binaryEqRelation.getRelationSymbol();
			final Relation relation = getRelation(lhs, rhs);

			if ((relation == Relation.EQUAL && termRelationSymbol == RelationSymbol.EQ)
					|| (relation == Relation.DISTINCT && termRelationSymbol == RelationSymbol.DISTINCT)) {
				return Implication.IMPLIED;
			} else {
				return Implication.UNKNOWN;
			}

		} else {
			throw new AssertionError("term is not a binary equality relation");
		}
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
