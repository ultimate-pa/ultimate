package de.uni_freiburg.informatik.ultimate.lib.smtlibutils.egraph;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.CommuhashUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.binaryrelation.BinaryEqualityRelation;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.binaryrelation.RelationSymbol;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.smtinterpol.util.DAGSize;
import de.uni_freiburg.informatik.ultimate.util.datastructures.CrossProducts;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ImmutableSet;
import de.uni_freiburg.informatik.ultimate.util.datastructures.UnionFind;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

public class EGraph {
	private final IUltimateServiceProvider mServices;
	private final ManagedScript mMgdScript;

	/**
	 * Internal {@link UnionFind} data structure to partition {@link Term}s into equivalence classes.
	 **/
	private final UnionFind<Term> mUnionFind;

	/**
	 * Keeps track of {@link Term}s we know to be distinct.
	 **/
	private final HashMap<ImmutableSet<Term>, HashSet<Term>> mDistinctSets;

	/**
	 * Partition of all select terms by their array.
	 *
	 * This is represented with a map from a set containing an array and all arrays in its equivalence class, to a set
	 * of all select terms which contain the array (or an equivalent array) as its array argument.
	 **/
	private final HashMap<ImmutableSet<Term>, Set<ApplicationTerm>> mSelectArrayPartition;
	/**
	 * Partition of all select terms by their index.
	 *
	 * This is represented with a map from a set containing an index of an array and all indices in its equivalence
	 * class, to a set of all select terms which contain the index (or an equivalent index) as its index argument.
	 **/
	private final HashMap<ImmutableSet<Term>, Set<ApplicationTerm>> mSelectIndexPartition;

	/**
	 * Constructs a new empty egraph
	 **/
	public EGraph(final ManagedScript mgdScript, final IUltimateServiceProvider services) {
		mUnionFind = new UnionFind<>(new MinimalSizeElementComparator());
		mDistinctSets = new HashMap<>();
		mSelectArrayPartition = new HashMap<>();
		mSelectIndexPartition = new HashMap<>();

		mMgdScript = mgdScript;
		mServices = services;

	}

	/**
	 * Comparator which orders {@link Term}s by increasing size. If two Terms of size one are ordered using the order
	 * literal < constant symbol < variable. Otherwise, in all other cases we order the Terms using
	 * {@link CommuhashUtils#HASH_BASED_COMPERATOR}
	 **/
	private static class MinimalSizeElementComparator implements Comparator<Term> {
		private final DAGSize mDagSize;

		public MinimalSizeElementComparator() {
			mDagSize = new DAGSize();
		}

		/**
		 * Helper method that ranks {@link Term}s of size one, using the order literal < constant symbol < variable.
		 **/
		private static int rankTermOfSizeOne(final Term term) {
			if (SmtUtils.isFalseLiteral(term)) {
				return 0;
			} else if (SmtUtils.isTrueLiteral(term)) {
				return 1;
			} else if (term instanceof ConstantTerm) {
				return 2;
			} else if (SmtUtils.isConstant(term)) {
				return 3;
			} else if (term instanceof TermVariable) {
				return 4;
			} else {
				throw new AssertionError("Unexpected term of size one");
			}
		}

		/**
		 * Helper method that compares two {@link Term}s of size one using the order literal < constant symbol <
		 * variable, breaking ties lexicographically.
		 **/
		private static int compareTermsOfSizeOne(final Term term1, final Term term2) {
			if (rankTermOfSizeOne(term1) < rankTermOfSizeOne(term2)) {
				return -1;
			} else if (rankTermOfSizeOne(term1) > rankTermOfSizeOne(term2)) {
				return 1;
			} else {
				return term1.toString().compareTo(term2.toString());
			}
		}

		@Override
		public int compare(final Term term1, final Term term2) {
			if (term1.equals(term2)) {
				return 0;
			}
			if (mDagSize.treesize(term1) < mDagSize.treesize(term2)) {
				return -1;
			} else if (mDagSize.treesize(term1) > mDagSize.treesize(term2)) {
				return 1;
			} else { // tiebreaking
				if (mDagSize.treesize(term1) == 1) {
					return compareTermsOfSizeOne(term1, term2);
				} else {
					return CommuhashUtils.HASH_BASED_COMPERATOR.compare(term1, term2);
				}
			}
		}

	}

	/**
	 * Adds select terms to the datastructure, creating new partitions for their arguments if necessary.
	 **/
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

	/**
	 * Adds terms to the datastructure.
	 **/
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

	/**
	 * Creates an egraph-like datastructure from a formula which is assumed to be of the form of a list of conjuncts.
	 **/
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

	/**
	 * Triple representing a union operation where E is the union of A and B.
	 **/
	// custom triple as there are no triples in java
	private static class UnionOperation {
		public ImmutableSet<Term> mA;
		public ImmutableSet<Term> mB;
		public ImmutableSet<Term> mE;

		public UnionOperation(final ImmutableSet<Term> A, final ImmutableSet<Term> B, final ImmutableSet<Term> E) {
			mA = A;
			mB = B;
			mE = E;
		}
	}

	/**
	 * This method finds all possible unions of select terms following a union of two terms.
	 **/
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
			findImpliedSelectUnions(unionOp.mA, unionOp.mB, unionOp.mE);
		}
	}

	/**
	 * Method that unions two sets of select terms while maintaining the required array and index partitions
	 **/
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

	/**
	 * Method that maintains the distinct terms datastructure for a given union.
	 **/
	private void unionDistinctTerms(final ImmutableSet<Term> A, final ImmutableSet<Term> B,
			final ImmutableSet<Term> E) {
		final HashSet<Term> newDistinct = mDistinctSets.getOrDefault(A, new HashSet<>());
		newDistinct.addAll(mDistinctSets.getOrDefault(B, new HashSet<>()));
		mDistinctSets.remove(A);
		mDistinctSets.remove(B);
		mDistinctSets.put(E, newDistinct);
	}

	/**
	 * Union two terms that are on either side of an equality
	 **/
	private void unionWithImplied(final Term a, final Term b) {
		final ImmutableSet<Term> A = mUnionFind.getContainingSet(a);
		final ImmutableSet<Term> B = mUnionFind.getContainingSet(b);
		final boolean unioned = union(a, b);
		if (unioned) {
			final ImmutableSet<Term> E = mUnionFind.getContainingSet(a);
			findImpliedSelectUnions(A, B, E);
		}
	}

	/**
	 * Union two terms and create A, B, and E sets for select and distinct handling
	 **/
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

	/**
	 * Whether a term is implied by the egraph or we do not know if it is implied.
	 **/
	public enum Implication {
		IMPLIED, UNKNOWN
	}

	/**
	 * Method that given a term, returns IMPLIED or UNKNOWN after checking if the given term is implied by the egraph
	 **/
	public Implication isImplied(final Term term) {
		final BinaryEqualityRelation binaryEqRelation = BinaryEqualityRelation.convert(term);
		if (binaryEqRelation != null) {
			final Term lhs = binaryEqRelation.getLhs();
			final Term rhs = binaryEqRelation.getRhs();

			final RelationSymbol termRelationSymbol = binaryEqRelation.getRelationSymbol();
			final EquivalenceState relation = getRelation(lhs, rhs);

			if ((relation == EquivalenceState.EQUAL && termRelationSymbol == RelationSymbol.EQ)
					|| (relation == EquivalenceState.DISTINCT && termRelationSymbol == RelationSymbol.DISTINCT)) {
				return Implication.IMPLIED;
			} else {
				return Implication.UNKNOWN;
			}

		} else {
			throw new AssertionError("term is not a binary equality relation");
		}
	}

	/**
	 * Checks if both terms are in the same equivalence class
	 **/
	public boolean areEquivalent(final Term a, final Term b) {
		if (mUnionFind.find(a) == null) {
			return false;
		}
		return mUnionFind.getContainingSet(a).equals(mUnionFind.getContainingSet(b));
	}

	/**
	 * Checks if two terms are known to be distinct.
	 **/
	public boolean areDistinct(final Term a, final Term b) {
		if (!(mDistinctSets.containsKey(mUnionFind.getContainingSet(a)))
				|| !(mDistinctSets.containsKey(mUnionFind.getContainingSet(b)))) {
			return false;
		}
		return mDistinctSets.get(mUnionFind.getContainingSet(a)).contains(b)
				|| mDistinctSets.get(mUnionFind.getContainingSet(b)).contains(a);

	}

	/**
	 * Whether two terms can be found by the egraph to be equivalent, distinct, or we know nothing about their
	 * equivalence.
	 **/
	public enum EquivalenceState {
		EQUAL, DISTINCT, UNKNOWN
	}

	public EquivalenceState getRelation(final Term a, final Term b) {
		if (areEquivalent(a, b)) {
			return EquivalenceState.EQUAL;
		} else if (areDistinct(a, b)) {
			return EquivalenceState.DISTINCT;
		} else {
			return EquivalenceState.UNKNOWN;
		}
	}

}
