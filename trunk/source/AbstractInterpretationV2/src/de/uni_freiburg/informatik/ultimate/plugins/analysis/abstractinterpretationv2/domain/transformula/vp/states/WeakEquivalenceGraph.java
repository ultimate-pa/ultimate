package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.states;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.function.Consumer;
import java.util.function.Predicate;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.ArrayIndex;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.MultiDimensionalSort;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.IEqNodeIdentifier;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements.IEqFunctionIdentifier;
import de.uni_freiburg.informatik.ultimate.util.datastructures.CongruenceClosure;
import de.uni_freiburg.informatik.ultimate.util.datastructures.CrossProducts;
import de.uni_freiburg.informatik.ultimate.util.datastructures.Doubleton;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

/**
	 * (short: weq graph)
	 *
	 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
	 *
	 */
public class WeakEquivalenceGraph<ACTION extends IIcfgTransition<IcfgLocation>,
			NODE extends IEqNodeIdentifier<NODE, FUNCTION>,
			FUNCTION extends IEqFunctionIdentifier<NODE, FUNCTION>> {
		/**
		 *
		 */
//		private final EqConstraint<ACTION, NODE, FUNCTION> mEqConstraint;

	EqConstraintFactory<ACTION, NODE, FUNCTION> mFactory;

		private Map<Doubleton<FUNCTION>, WeakEquivalenceEdgeLabel> mWeakEquivalenceEdges;

		private final HashRelation<FUNCTION, FUNCTION> mArrayEqualities;

		/**
		 * The WeqCongruenceClosure that this weq graph is part of. This may be null, if we use this weq graph as an
		 * intermediate, for example during a join or meet operation.
		 */
		private WeqCongruenceClosure<ACTION, NODE, FUNCTION> mPartialArrangement;

		/**
		 * Constructs an empty WeakEquivalenceGraph
		 * @param factory
		 * @param eqConstraint TODO
		 */
		public WeakEquivalenceGraph(final WeqCongruenceClosure<ACTION, NODE, FUNCTION> pArr,
				final EqConstraintFactory<ACTION, NODE, FUNCTION> factory) {
//			mEqConstraint = eqConstraint;
			mPartialArrangement = pArr;
			mWeakEquivalenceEdges = new HashMap<>();
			mArrayEqualities = new HashRelation<>();
			assert factory != null;
			mFactory = factory;
			assert sanityCheck();
		}



		//		public HashRelation<FUNCTION, FUNCTION> getArrayEqualities() {
		//			assert hasArrayEqualities();
		//			return mArrayEqualities;
		//		}

		/**
		 *
		 * @param weakEquivalenceEdges caller needs to make sure that no one else has a reference to this map -- we are
		 * 		not making a copy here.
		 * @param arrayEqualities for the special case of an intermediate weq graph during the meet operation where an
		 *      edge label became "bottom"
		 * @param factory
		 * @param eqConstraint TODO
		 */
		private WeakEquivalenceGraph(//final EqConstraint<ACTION, NODE, FUNCTION> eqConstraint,
				final WeqCongruenceClosure<ACTION, NODE, FUNCTION> pArr,
				final Map<Doubleton<FUNCTION>, WeakEquivalenceEdgeLabel> weakEquivalenceEdges,
				final HashRelation<FUNCTION, FUNCTION> arrayEqualities,
				final EqConstraintFactory<ACTION, NODE, FUNCTION> factory) {
//			mEqConstraint = eqConstraint;
			mWeakEquivalenceEdges = weakEquivalenceEdges;
			mArrayEqualities = arrayEqualities;
			assert factory != null;
			mFactory = factory;
		}

		/**
		 * Copy constructor
		 * @param weakEquivalenceGraph
		 * @param factory
		 * @param eqConstraint TODO
		 */
		public WeakEquivalenceGraph(//final EqConstraint<ACTION, NODE, FUNCTION> eqConstraint,
				final WeqCongruenceClosure<ACTION, NODE, FUNCTION> pArr,
				final WeakEquivalenceGraph<ACTION, NODE, FUNCTION> weakEquivalenceGraph) {
//				final EqConstraintFactory<ACTION, NODE, FUNCTION> factory) {
//			this(mEqConstraint, weakEquivalenceGraph, true);
			this(pArr, weakEquivalenceGraph, true);
			assert weakEquivalenceGraph.mArrayEqualities.isEmpty();
		}

		WeakEquivalenceGraph(
				final WeqCongruenceClosure<ACTION, NODE, FUNCTION> pArr,
				final WeakEquivalenceGraph<ACTION, NODE, FUNCTION> weqMeet,
				final boolean forgetArrayEqualities) {
//			mEqConstraint = eqConstraint;
			mPartialArrangement = pArr;
			mArrayEqualities = forgetArrayEqualities ?
					new HashRelation<>() :
						new HashRelation<>(weqMeet.mArrayEqualities);
			mWeakEquivalenceEdges = new HashMap<>();
			for (final Entry<Doubleton<FUNCTION>, WeakEquivalenceEdgeLabel> weqEdge
						: weqMeet.mWeakEquivalenceEdges.entrySet()) {
				mWeakEquivalenceEdges.put(weqEdge.getKey(), new WeakEquivalenceEdgeLabel(weqEdge.getValue()));
			}
			mFactory = weqMeet.mFactory;
			assert sanityCheck();
		}

//		void setGroundPartialArrangement(final WeqCongruenceClosure gpa) {
//			mPartialArrangement = gpa;
//		}

		/**
		 * Called when an equality "node1 = node2" has just been reported.
		 * Checks if there is a weak equivalence edge that allows a propagation because of that equality.
		 * Analogous to the standard forward congruence propagation that is done in CongruenceClosure when an element
		 * equality has been added.
		 *
		 * @param node1
		 * @param node2
		 * @return set of equalities that can be propagated (design decision: let modifications of the ground partial
		 * 		arrangement be done "outside", in EqConstraint)
		 */
		public  Set<Doubleton<NODE>> getWeakCongruencePropagations(final NODE node1, final NODE node2) {
			final Set<Doubleton<NODE>> equalitiesToBePropagated = new HashSet<>();

			for (final Entry<Doubleton<FUNCTION>, WeakEquivalenceEdgeLabel> edge : mWeakEquivalenceEdges.entrySet()) {

				final FUNCTION func1 = edge.getKey().getOneElement();
				final FUNCTION func2 = edge.getKey().getOtherElement();

				equalitiesToBePropagated.addAll(
						helper(func1, func2, node1, node2, edge.getValue(), mPartialArrangement));
				equalitiesToBePropagated.addAll(
						helper(func2, func1, node1, node2, edge.getValue(), mPartialArrangement));
			}
			return equalitiesToBePropagated;
		}

		private Set<Doubleton<NODE>> helper(final FUNCTION func1, final FUNCTION func2, final NODE node1,
				final NODE node2, final WeakEquivalenceEdgeLabel label, final CongruenceClosure<NODE, FUNCTION> pa) {
			final Set<Doubleton<NODE>> newEqualitiesToBePropagated = new HashSet<>();

			final Set<NODE> e1CcParsA = pa.getCcPars(func1, mPartialArrangement.getRepresentativeElement(node1), false);
			final Set<NODE> e2CcParsA = pa.getCcPars(func2, mPartialArrangement.getRepresentativeElement(node2), false);

			if (e1CcParsA == null || e2CcParsA == null) {
				// nothing to do
				return Collections.emptySet();
			}

			{
				final Set<NODE> e1CcParsCopy = new HashSet<>(e1CcParsA);
				final Set<NODE> e2CcParsCopy = new HashSet<>(e2CcParsA);
				for (final NODE ccpar1 : e1CcParsCopy) {
					for (final NODE ccpar2 : e2CcParsCopy) {
						// insert forward congruence

						if (!pa.argumentsAreCongruent(ccpar1, ccpar2)) {
							continue;
						}
						if (!label.impliesEqualityOnThatPosition(ccpar1.getArguments())) {

						}
						newEqualitiesToBePropagated.add(new Doubleton<>(ccpar1, ccpar2));
					}
				}
			}
			return newEqualitiesToBePropagated;
		}


		public  Entry<FUNCTION, FUNCTION> pollArrayEquality() {
			if (!hasArrayEqualities()) {
				throw new IllegalStateException("check hasArrayEqualities before calling this method");
			}
			final Entry<FUNCTION, FUNCTION> en = mArrayEqualities.iterator().next();
			mArrayEqualities.removePair(en.getKey(), en.getValue());
			return en;
		}

		public void reportChangeInGroundPartialArrangement(final Predicate<CongruenceClosure<NODE, FUNCTION>> action) {
			final Map<Doubleton<FUNCTION>, WeakEquivalenceEdgeLabel> weqCopy = new HashMap<>(mWeakEquivalenceEdges);
			for (final Entry<Doubleton<FUNCTION>, WeakEquivalenceEdgeLabel> edge : weqCopy.entrySet())  {
				final boolean becameInconsistent = edge.getValue().reportChangeInGroundPartialArrangement(action);
				if (becameInconsistent) {
					// edge label became inconsistent --> remove the weq edge, add a strong equivalence instead
					mWeakEquivalenceEdges.remove(edge.getKey());
					mArrayEqualities.addPair(edge.getKey().getOneElement(), edge.getKey().getOtherElement());
				}
			}

		}

//		/**
//		 * Checks if any weak equivalence-edge label is inconsistent with the current mPartialArrangement.
//		 * If so, it removes the edge and adds an array equality.
//		 *
//		 * TODO: rework
//		 *
//		 * @return true iff weak equivalence graph changed during this operation
//		 */
//		public boolean applyChangesInGroundPartialArrangement() {
//			assert mArrayEqualities.isEmpty();
//			boolean madeChanges = false;
//			final HashMap<Doubleton<FUNCTION>, WeakEquivalenceEdgeLabel> edgesCopy =
//					new HashMap<>(mWeakEquivalenceEdges);
//			for (final Entry<Doubleton<FUNCTION>, WeakEquivalenceEdgeLabel> edge : edgesCopy.entrySet()) {
//				if (edge.getValue().isInconsistentWith(mPartialArrangement)) {
//					mWeakEquivalenceEdges.remove(edge.getKey());
//					mArrayEqualities.addPair(edge.getKey().getOneElement(), edge.getKey().getOtherElement());
//					madeChanges |= true;
//				}
//			}
//			return madeChanges;
//		}

		public void projectFunction(final FUNCTION func, final CongruenceClosure<NODE, FUNCTION> groundPartialArrangement) {
			final Map<Doubleton<FUNCTION>, WeakEquivalenceEdgeLabel> edgesCopy = new HashMap<>(mWeakEquivalenceEdges);
			for (final Entry<Doubleton<FUNCTION>, WeakEquivalenceEdgeLabel> en : edgesCopy.entrySet()) {
				if (en.getKey().getOneElement().equals(func) || en.getKey().getOtherElement().equals(func)) {
					mWeakEquivalenceEdges.remove(en.getKey());
				} else {
					en.getValue().projectFunction(func, groundPartialArrangement);
				}
			}
			assert sanityCheck();
		}

		/**
		 * Project the given element from all weak equivalence edges.
		 * We aim to keep information about the projected element from the ground partial arrangement. We take the
		 * following steps to compute the new edge labels.
		 *  <li> compute the meet with the ground partial arrangement
		 *  <li> project out the variable to be projected elem
		 *  <li> project out all constraints that do not contain a weq-variable
		 *
		 * @param elem
		 * @param groundPartialArrangement
		 */
		public void projectElement(final NODE elem, final CongruenceClosure<NODE, FUNCTION> groundPartialArrangement) {
			for (final Entry<Doubleton<FUNCTION>, WeakEquivalenceEdgeLabel> en : mWeakEquivalenceEdges.entrySet()) {
				en.getValue().projectElement(elem, groundPartialArrangement);
			}
			assert sanityCheck();
		}

		public void renameVariables(final Map<Term, Term> substitutionMapping) {
			final HashMap<Doubleton<FUNCTION>, WeakEquivalenceEdgeLabel> weqEdgesCopy =
					new HashMap<>(mWeakEquivalenceEdges);
			for (final Entry<Doubleton<FUNCTION>, WeakEquivalenceEdgeLabel> en : weqEdgesCopy.entrySet()) {
				mWeakEquivalenceEdges.remove(en.getKey());

				final Doubleton<FUNCTION> newDton = new Doubleton<>(
						en.getKey().getOneElement().renameVariables(substitutionMapping),
						en.getKey().getOtherElement().renameVariables(substitutionMapping));
				en.getValue().renameVariables(substitutionMapping); //TODO : is doing it in-place a smart choice??
				mWeakEquivalenceEdges.put(newDton, en.getValue());
			}
		}

/**
		 *
		 * @param other
		 * @param newPartialArrangement the joined partialArrangement, we need this because the edges of the the new
		 * 		weq graph have to be between the new equivalence representatives TODO
		 * @return
		 */
		WeakEquivalenceGraph<ACTION, NODE, FUNCTION> join(final WeakEquivalenceGraph<ACTION, NODE, FUNCTION> other) {
			final Map<Doubleton<FUNCTION>, WeakEquivalenceEdgeLabel> newWeakEquivalenceEdges = new HashMap<>();
			for (final Entry<Doubleton<FUNCTION>, WeakEquivalenceEdgeLabel> thisWeqEdge
					: this.mWeakEquivalenceEdges.entrySet()) {
				final WeakEquivalenceEdgeLabel correspondingWeqEdgeInOther =
						other.mWeakEquivalenceEdges.get(thisWeqEdge.getKey());
				if (correspondingWeqEdgeInOther == null) {
					continue;
				}
				newWeakEquivalenceEdges.put(thisWeqEdge.getKey(),
						thisWeqEdge.getValue().union(correspondingWeqEdgeInOther));

			}
			return new WeakEquivalenceGraph<ACTION, NODE, FUNCTION>(null, newWeakEquivalenceEdges, new HashRelation<>(), mFactory);
		}

		WeakEquivalenceGraph<ACTION, NODE, FUNCTION> meet(final WeakEquivalenceGraph<ACTION, NODE, FUNCTION> other,
				final CongruenceClosure<NODE, FUNCTION> newPartialArrangement) {
			final Map<Doubleton<FUNCTION>, WeakEquivalenceEdgeLabel> newWeakEquivalenceEdges = new HashMap<>();
			final HashRelation<FUNCTION, FUNCTION> newArrayEqualities = new HashRelation<>();
			/*
			 * for clarity we distinguish three cases for any two nodes (n1, n2) in the weq-graph
			 *  <li> there is an edge (n1, I, n2) in this but not in other
			 *  <li> there is an edge  (n1, I, n2) in other but not in this
			 *  <li> there are edges (n1, I, n2), (n1, I', n2) in both
			 */
			// case 1
			for (final Entry<Doubleton<FUNCTION>, WeakEquivalenceEdgeLabel> thisWeqEdge
					: this.mWeakEquivalenceEdges.entrySet()) {
				final WeakEquivalenceEdgeLabel correspondingWeqEdgeInOther =
						other.mWeakEquivalenceEdges.get(thisWeqEdge.getKey());
				if (correspondingWeqEdgeInOther != null) {
					// case 3 applies
					continue;
				}
				final WeakEquivalenceEdgeLabel newEdgeLabel = thisWeqEdge.getValue();
				if (newEdgeLabel.isInconsistentWith(newPartialArrangement)) {
					// edge label became inconsistent -- add a strong equivalence instead of a weak one
					newArrayEqualities.addPair(thisWeqEdge.getKey().getOneElement(),
							thisWeqEdge.getKey().getOtherElement());
					continue;
				}
				newEdgeLabel.updateWrtPartialArrangement(newPartialArrangement);
				newWeakEquivalenceEdges.put(thisWeqEdge.getKey(), newEdgeLabel);
			}
			// case 2
			for (final Entry<Doubleton<FUNCTION>, WeakEquivalenceEdgeLabel> otherWeqEdge
					: other.mWeakEquivalenceEdges.entrySet()) {
				final WeakEquivalenceEdgeLabel correspondingWeqEdgeInThis =
						this.mWeakEquivalenceEdges.get(otherWeqEdge.getKey());
				if (correspondingWeqEdgeInThis != null) {
					// case 3 applies
					continue;
				}
				final WeakEquivalenceEdgeLabel newEdgeLabel = otherWeqEdge.getValue();
				if (newEdgeLabel.isInconsistentWith(newPartialArrangement)) {
					// edge label became inconsistent -- add a strong equivalence instead of a weak one
					newArrayEqualities.addPair(otherWeqEdge.getKey().getOneElement(),
							otherWeqEdge.getKey().getOtherElement());
					continue;
				}
				newEdgeLabel.updateWrtPartialArrangement(newPartialArrangement);
				newWeakEquivalenceEdges.put(otherWeqEdge.getKey(), newEdgeLabel);

			}
			// case 3
			for (final Entry<Doubleton<FUNCTION>, WeakEquivalenceEdgeLabel> thisWeqEdge
					: this.mWeakEquivalenceEdges.entrySet()) {
				final WeakEquivalenceEdgeLabel correspondingWeqEdgeInOther =
						other.mWeakEquivalenceEdges.get(thisWeqEdge.getKey());
				if (correspondingWeqEdgeInOther == null) {
					// not case 3
					continue;
				}
				final WeakEquivalenceEdgeLabel newEdgeLabel = thisWeqEdge.getValue().meet(correspondingWeqEdgeInOther);
				if (newEdgeLabel.isInconsistentWith(newPartialArrangement)) {
					// edge label became inconsistent -- add a strong equivalence instead of a weak one
					newArrayEqualities.addPair(thisWeqEdge.getKey().getOneElement(),
							thisWeqEdge.getKey().getOtherElement());
					continue;
				}
				newEdgeLabel.updateWrtPartialArrangement(newPartialArrangement);
				newWeakEquivalenceEdges.put(thisWeqEdge.getKey(), newEdgeLabel);
			}
			final WeakEquivalenceGraph<ACTION, NODE, FUNCTION> result =
					new WeakEquivalenceGraph<ACTION, NODE, FUNCTION>(null, newWeakEquivalenceEdges, newArrayEqualities,
							mFactory);
			result.close();
			return result;
		}

		boolean hasArrayEqualities() {
			return !mArrayEqualities.isEmpty();
		}

		/**
		 *
		 * @return true iff this operation performed any changes on this weq graph
		 */
		private boolean close() {
			if (mWeakEquivalenceEdges.isEmpty()) {
				return false;
			}
			final FloydWarshall<FUNCTION, WeakEquivalenceEdgeLabel> fw =
					new FloydWarshall<>(WeakEquivalenceEdgeLabel::isStrongerThan,
							WeakEquivalenceEdgeLabel::union,
							new WeakEquivalenceEdgeLabel(),
							mWeakEquivalenceEdges,
							(final WeakEquivalenceEdgeLabel lab) -> new WeakEquivalenceEdgeLabel(lab));
			mWeakEquivalenceEdges = fw.getResult();
			return fw.performedChanges();
		}

		/**
		 *
		 * @return true if this graph has no constraints/is tautological
		 */
		public boolean isEmpty() {
			return mWeakEquivalenceEdges.isEmpty() && !hasArrayEqualities();
		}

		/**
		 *
		 * @param func1 edge source (edge is symmetric)
		 * @param func2 edge target (edge is symmetric)
		 * @param nodes position where FUNCTIONs may differ
		 * @return
		 */
		public boolean reportWeakEquivalence(final FUNCTION func1, final FUNCTION func2, final List<NODE> nodes) {
			assert func1.getArity() == func2.getArity();
			final Doubleton<FUNCTION> sourceAndTarget = new Doubleton<FUNCTION>(func1, func2);
			WeakEquivalenceEdgeLabel edgeLabel = mWeakEquivalenceEdges.get(sourceAndTarget);
			if (edgeLabel == null) {
//				edgeLabel = new WeakEquivalenceEdgeLabel(func1.getArity());
				edgeLabel = new WeakEquivalenceEdgeLabel();
				mWeakEquivalenceEdges.put(sourceAndTarget, edgeLabel);
			}
			final CongruenceClosure<NODE, FUNCTION> newConstraint = computeWeqConstraintForIndex(nodes);
			final boolean stateChanged = edgeLabel.addConstraint(newConstraint);
			assert sanityCheck();
			return stateChanged;
		}

		/**
		 * Given a (multidimensional) index, compute the corresponding annotation for a weak equivalence edge.
		 *
		 * Example:
		 * for (i1, .., in), this should return (q1 = i1, ..., qn = in) as a list of CongruenceClosures.
		 *  (where qi is the variable returned by getWeqVariableForDimension(i))
		 *
		 * @param nodes
		 * @return
		 */
		private CongruenceClosure<NODE, FUNCTION> computeWeqConstraintForIndex(final List<NODE> nodes) {
			final CongruenceClosure<NODE, FUNCTION> result = new CongruenceClosure<>();
			for (int i = 0; i < nodes.size(); i++) {
				final NODE ithNode = nodes.get(i);
				result.reportEquality(mFactory.getWeqVariableNodeForDimension(i, ithNode.getTerm().getSort()), ithNode);
			}
			return result;
		}

		/**
		 *
		 * @param func1 edge source (edge is symmetric)
		 * @param func2 edge target (edge is symmetric)
		 * @param partialArrangements partial arrangement describing where FUNCTIONs may differ
		 * @return
		 */
		public boolean reportWeakEquivalence(final FUNCTION func1, final FUNCTION func2,
				final CongruenceClosure<NODE, FUNCTION>... partialArrangements) {
			assert false;
			return false;
		}

		/**
		 *
		 * @param func1 edge source (edge is symmetric)
		 * @param func2 edge target (edge is symmetric)
		 * @param partialArrangements disjunction of partial arrangement describing where FUNCTIONs may differ
		 * @return
		 */
		public boolean reportWeakEquivalence(final FUNCTION func1, final FUNCTION func2,
				final Collection<CongruenceClosure<NODE, FUNCTION>>... partialArrangements) {
			assert false;
			return false;
		}


		public boolean isStrongerThan(final WeakEquivalenceGraph<ACTION, NODE, FUNCTION> other) {
			for (final Entry<Doubleton<FUNCTION>, WeakEquivalenceEdgeLabel> otherWeqEdgeAndLabel
					: other.mWeakEquivalenceEdges.entrySet()) {
				final WeakEquivalenceEdgeLabel correspondingWeqEdgeInThis =
						this.mWeakEquivalenceEdges.get(otherWeqEdgeAndLabel.getKey());
				if (correspondingWeqEdgeInThis == null) {
					// "other" has an edge that "this" does not -- this cannot be stronger
					return false;
				}
				// if the this-edge is strictly weaker than the other-edge, we have a counterexample
				if (!correspondingWeqEdgeInThis.isStrongerThan(otherWeqEdgeAndLabel.getValue())) {
					return false;
				}
			}
			return true;
		}

		/**
		 * Computes an implicitly conjunctive list of weak equivalence constraints. Each element in the list is the
		 * constrained induced by one weak equivalence edge in this weq graph.
		 *
		 * @param script
		 * @return
		 */
		public List<Term> getWeakEquivalenceConstraintsAsTerms(final Script script) {
			assert mArrayEqualities == null || mArrayEqualities.isEmpty();
			final List<Term> result = new ArrayList<>();
			for (final Entry<Doubleton<FUNCTION>, WeakEquivalenceEdgeLabel> edge : mWeakEquivalenceEdges.entrySet()) {
				final List<Term> dnfAsCubeList = new ArrayList<>();
				dnfAsCubeList.addAll(edge.getValue().toDNF(script));

				final Term arrayEquation = computeArrayEquation(script, edge.getKey().getOneElement(),
						edge.getKey().getOtherElement());
				dnfAsCubeList.add(arrayEquation);

				final Term edgeFormula = SmtUtils.quantifier(script, QuantifiedFormula.FORALL,
						computeWeqIndicesForArray(edge.getKey().getOneElement()), SmtUtils.or(script, dnfAsCubeList));
				result.add(edgeFormula);
			}
			return result;
		}

		/**
		 * For the two given arrays a, b, this computes an equation a[q1, .., qn] = b[q1, ..,qn] where qi are the
		 * implicitly quantified variables of our weak equivalences (managed by getWeqVariables for dimension).
		 * Uses the array's multidimensional sort to get the right variables.
		 *
		 * @param script
		 * @param array1
		 * @param array2
		 * @return
		 */
		private Term computeArrayEquation(final Script script, final FUNCTION array1, final FUNCTION array2) {
			assert array1.getTerm().getSort().equals(array2.getTerm().getSort());
			final List<Term> indexEntries = computeWeqIndicesForArray(array1).stream().map(tv -> (Term) tv)
					.collect(Collectors.toList());
			final ArrayIndex index = new ArrayIndex(indexEntries);

			final Term select1 = SmtUtils.multiDimensionalSelect(script, array1.getTerm(), index);
			final Term select2 = SmtUtils.multiDimensionalSelect(script, array2.getTerm(), index);

			return SmtUtils.binaryEquality(script, select1, select2);
		}

		private List<TermVariable> computeWeqIndicesForArray(final FUNCTION array1) {
			final MultiDimensionalSort mdSort = new MultiDimensionalSort(array1.getTerm().getSort());

			final List<TermVariable> indexEntries = new ArrayList<>();
			for (int i = 0; i < array1.getArity(); i++) {
				indexEntries.add(mFactory.getWeqVariableForDimension(i, mdSort.getIndexSorts().get(i)));
			}
			return indexEntries;
		}

		@Override
		public String toString() {
			return mWeakEquivalenceEdges.toString();
		}


		boolean sanityCheck() {

//			assert mPartialArrangement != null;

			assert mFactory != null : "factory is needed for the sanity check..";

			/*
			 * check that no weak equivalence edge contains an ELEM or FUNCTION that is not known to mPartialArrangement
			 * or is one of the special quantified variables from getVariableForDimension(..).
			 */
			if (mPartialArrangement != null) {
				for (final Entry<Doubleton<FUNCTION>, WeakEquivalenceEdgeLabel> edge :
						mWeakEquivalenceEdges.entrySet()) {
					if (!mPartialArrangement.hasFunction(edge.getKey().getOneElement())
							|| !mPartialArrangement.hasFunction(edge.getKey().getOtherElement())) {
						assert false;
						return false;
					}
					if (!mPartialArrangement.getAllElements().containsAll(
							edge.getValue().getAppearingNodes().stream()
							.filter(node -> !mFactory.getAllWeqNodes().contains(node)).collect(Collectors.toSet()))) {
						assert false;
						return false;
					}
					if (!mPartialArrangement.getAllFunctions().containsAll(edge.getValue().getAppearingFunctions())) {
						assert false;
						return false;
					}
				}
			}

			/*
			 * Check that all the edges are between equivalence classes of mPartialArrangement
			 */

			/*
			 * Check that none of the edges has the same source and target (is a self-loop).
			 */
			for (final Doubleton<FUNCTION> dton : mWeakEquivalenceEdges.keySet()) {
				if (dton.getOneElement().equals(dton.getOtherElement())) {
					assert false;
					return false;
				}
			}

			/*
			 * check completeness of the graph ("triangle inequality")
			 */


			// is closed/triangle inequation holds
//			if (mPartialArrangement != null) {
//				if (close()) {
//					assert false;
//					return false;
//				}
//			}

			return true;
		}

		/**
		 * Represents an edge label in the weak equivalence graph.
		 * An edge label connects two arrays of the same arity(dimensionality) #a.
		 * An edge label is a tuple of length #a.
		 * Each tuple element is a set of partial arrangements. The free variables in the partial arrangements are the
		 * variables of the EqConstraint together with #a special variables that are implicitly universally quantified
		 * and range over the array positions.
		 *
		 */
		class WeakEquivalenceEdgeLabel {

			private final List<CongruenceClosure<NODE, FUNCTION>> mLabel;
			private final List<CongruenceClosure<NODE, FUNCTION>> mLabelWithGroundPa;

			/**
			 * Constructs an empty edge. (labeled "true")
			 */
			public WeakEquivalenceEdgeLabel() {
				mLabel = new ArrayList<>();
				mLabel.add(new CongruenceClosure<>());
				mLabelWithGroundPa = new ArrayList<>();
				if (mPartialArrangement != null) {
					mLabelWithGroundPa.add(new CongruenceClosure<>(mPartialArrangement));
				} else {
					mLabelWithGroundPa.add(new CongruenceClosure<>());
				}
				assert sanityCheck();
			}

			/**
			 * leaves mLabel, but construct mLabelWithgroundPa according to the given partial arrangement
			 * @param newPartialArrangement
			 */
			public void updateWrtPartialArrangement(final CongruenceClosure<NODE, FUNCTION> newPartialArrangement) {
				for (int i = 0; i < mLabel.size(); i++) {
					mLabelWithGroundPa.set(i, mLabel.get(i).meet(newPartialArrangement));
				}
			}

			/**
			 * Copy constructor.
			 *
			 * @param value
			 */
			public WeakEquivalenceEdgeLabel(final WeakEquivalenceEdgeLabel value) {
//				mArityOfArrays = value.mArityOfArrays;
				mLabel = new ArrayList<>(value.mLabel.size());
				mLabelWithGroundPa = new ArrayList<>();
//				for (final CongruenceClosure<NODE, FUNCTION> pa : value.mLabel) {
				for (int i = 0; i < value.mLabel.size(); i++) {
					mLabel.add(new CongruenceClosure<>(value.mLabel.get(i)));
					mLabelWithGroundPa.add(new CongruenceClosure<>(value.mLabelWithGroundPa.get(i)));
				}
				assert sanityCheck();
			}

			/**
			 * Construct a weak equivalence edge from a list of label contents.
			 *
			 * Does some simplifications.
			 *
			 * @param newLabelContents
			 */
			public WeakEquivalenceEdgeLabel(final List<CongruenceClosure<NODE, FUNCTION>> newLabelContents,
					final List<CongruenceClosure<NODE, FUNCTION>> newLabelWgpaContents) {

				mLabel = newLabelContents;
				mLabelWithGroundPa = newLabelWgpaContents;

				assert sanityCheck();
			}

			public boolean impliesEqualityOnThatPosition(final List<NODE> arguments) {
				for (int i = 0; i < mLabel.size(); i++) {
					final CongruenceClosure<NODE, FUNCTION> copy = new CongruenceClosure<>(mLabelWithGroundPa.get(i));
					for (int j = 0; i < arguments.size(); j++) {
						final NODE argJ = arguments.get(j);
						final NODE weqVar = WeakEquivalenceGraph.this.mFactory.getWeqVariableNodeForDimension(j, argJ.getTerm().getSort());
						copy.reportEquality(weqVar, argJ);
						if (copy.isInconsistent()) {
							break;
						}
					}

					if (copy.isInconsistent()) {
						// go on;
					} else {
						/*
						 * label did not become inconsistent when adding the equalities q1 = arg1, ... qn = argn
						 *  --> the weak equivalence is not strong enough to imply a[arg1, ..,argn] = b[arg1, .., argn]
						 *     (where a, b are the source and target of the weq edge)
						 */
						return false;
					}
				}
				return true;
			}

			/**
			 *
			 * @param reportX lambda, applying one of the CongruenceClosure.report functions to some nodes for a given
			 *   CongruenceClosure object
			 * @return true iff this label became inconsistent through the change in the ground partial arrangement
			 */
			public boolean reportChangeInGroundPartialArrangement(
					final Predicate<CongruenceClosure<NODE, FUNCTION>> reportX) {
				boolean allPasBecameInconsistent = true;

				final List<CongruenceClosure<NODE, FUNCTION>> labelCopy = new ArrayList<>(mLabel);
				final List<CongruenceClosure<NODE, FUNCTION>> labelWgpaCopy = new ArrayList<>(mLabelWithGroundPa);
				mLabel.clear();
				mLabelWithGroundPa.clear();

				for (int i = 0; i < labelCopy.size(); i++) {
					final CongruenceClosure<NODE, FUNCTION> currentLabelWgpa = labelWgpaCopy.get(i);
					final boolean res = reportX.test(currentLabelWgpa);

					if (!res) {
						/*
						 *  no change in mLabelWgpa[i] meet gpa -- this can happen, because labelWgpa might imply an
						 *  equality that is not present in gpa..
						 *
						 *  no checks need to be made here, anyway
						 */
						assert !currentLabelWgpa.isInconsistent();
						continue;
					}

					if (currentLabelWgpa.isInconsistent()) {
//						pasThatBecameInconsistent.add(i);
//						pasThatBecameInconsistent++;
					} else {
						allPasBecameInconsistent &= false;
						mLabel.add(labelCopy.get(i));
						mLabelWithGroundPa.add(labelWgpaCopy.get(i));
					}
				}

//				assert sanityCheck();
				if (allPasBecameInconsistent) {
					/*
					 *  the whole label became inconsistent
					 *  the weq graph must introduce a strong equality
					 *  --> report this via the return value
					 */
					return true;
				}
				return false;
			}

			private List<CongruenceClosure<NODE, FUNCTION>> simplifyPaDisjunction(
					final List<CongruenceClosure<NODE, FUNCTION>> newLabelContents) {
				// make a copy of the list, filter out false disjuncts
				List<CongruenceClosure<NODE, FUNCTION>> newLabel = new ArrayList<>(newLabelContents).stream()
						.filter(pa -> !pa.isInconsistent()).collect(Collectors.toList());

				// if there is any true disjunct, it will annihilate all the others
				if (newLabel.stream().anyMatch(pa -> pa.isTautological())) {
					newLabel = Collections.singletonList(new CongruenceClosure<>());
				}
				return newLabel;
			}

			/**
			 * Computes a DNF from this label as a List of conjunctive Terms.
			 *    The disjunction has the form \/_i pa_i
			 *
			 * @param script
			 * @return a DNF as a List of conjunctive Terms.
			 */
			public List<Term> toDNF(final Script script) {
				final List<Term> result = new ArrayList<>();
				for (final CongruenceClosure<NODE, FUNCTION> cc : mLabel) {
						final List<Term> cube = EqConstraint.partialArrangementToCube(script, cc);
						final Term cubeTerm = SmtUtils.and(script, cube);
						result.add(cubeTerm);
				}
				return result;
			}

			/**
			 *
			 *   do a meet of the given p arrangement with every entry of this label
			 *
			 * @param newConstraint
			 * @return true iff the operation made a change
			 */
			public boolean addConstraint(final CongruenceClosure<NODE, FUNCTION> newConstraint) {
				// TODO is it worth it to check, if the state has changed by this operation??
				final boolean stateChanged = true;
				for (int i = 0; i < mLabel.size(); i++) {
					mLabel.set(i, mLabel.get(i).meet(newConstraint));
					mLabelWithGroundPa.set(i, mLabelWithGroundPa.get(i).meet(newConstraint));
				}
				assert sanityCheck();
				return stateChanged;
			}

			public void renameVariables(final Map<Term, Term> substitutionMapping) {
//				for (final CongruenceClosure<NODE, FUNCTION> dimensionEntry : mLabel) {
				for (int i = 0; i < mLabel.size(); i++) {
					mLabel.get(i).transformElementsAndFunctions(node -> node.renameVariables(substitutionMapping),
							func -> func.renameVariables(substitutionMapping));
					mLabelWithGroundPa.get(i)
						.transformElementsAndFunctions(node -> node.renameVariables(substitutionMapping),
							func -> func.renameVariables(substitutionMapping));
				}
				assert sanityCheck();
			}

			/**
			 * Returns all NODEs that are used in this WeqEdgeLabel.
			 * Not including the special quantified variable's nodes.
			 * @return
			 */
			public Set<NODE> getAppearingNodes() {
				final Set<NODE> res = new HashSet<>();
				mLabel.forEach(pa -> res.addAll(pa.getAllElements()));
				return res;
			}

			public Set<FUNCTION> getAppearingFunctions() {
				final Set<FUNCTION> res = new HashSet<>();
				mLabel.forEach(pa -> res.addAll(pa.getAllFunctions()));
				return res;
			}

			public boolean isInconsistentWith(final CongruenceClosure<NODE, FUNCTION> newPartialArrangement) {
				// one consistent disjunct is a counterexample to inconsistency..
				for (final CongruenceClosure<NODE, FUNCTION> pa : mLabel) {
					if (!pa.meet(mPartialArrangement).isInconsistent()) {
						return false;
					}
				}
				return true;
			}

			public WeakEquivalenceEdgeLabel meet(final WeakEquivalenceEdgeLabel correspondingWeqEdgeInOther) {
				assert sanityCheck();

				final ArrayList<CongruenceClosure<NODE, FUNCTION>> newLabelContent = new ArrayList<>();

				final List<List<CongruenceClosure<NODE, FUNCTION>>> li = new ArrayList<>(2);
				li.add(mLabel);
				li.add(correspondingWeqEdgeInOther.mLabel);
				final List<List<CongruenceClosure<NODE, FUNCTION>>> cp = CrossProducts.crossProduct(li);

				for (final List<CongruenceClosure<NODE, FUNCTION>> pair : cp) {
					assert pair.size() == 2;
					newLabelContent.add(pair.get(0).meet(pair.get(1)));
				}

				final List<CongruenceClosure<NODE, FUNCTION>> newLabel = simplifyPaDisjunction(newLabelContent);

				final List<CongruenceClosure<NODE, FUNCTION>> newLabelWgpa = newLabel.stream()
						.map(pa -> pa.meet(mPartialArrangement)).collect(Collectors.toList());

				return new WeakEquivalenceEdgeLabel(newLabel, newLabelWgpa);
			}

			/**
			 * rule:  A isStrongerThan B
			 *     iff
			 *   forall ai exists bi. ai subseteq bi
			 * @param value
			 * @return
			 */
			public boolean isStrongerThan(final WeakEquivalenceEdgeLabel other) {
				for (final CongruenceClosure<NODE, FUNCTION> paThis : mLabel) {
					boolean existsWeaker = false;
					for (final CongruenceClosure<NODE, FUNCTION> paOther : other.mLabel) {
						if (paThis.isStrongerThan(paOther)) {
							existsWeaker = true;
							break;
						}
					}
					if (!existsWeaker) {
						return false;
					}
				}
				return true;
			}

			/**
			 * Computes a constraint which, for every dimension, has the union of the disjuncts of both input labels
			 *  (this and other).
			 * @param correspondingWeqEdgeInOther
			 * @return
			 */
			public WeakEquivalenceEdgeLabel union(final WeakEquivalenceEdgeLabel other) {
				// using a set to eliminate duplicates -- TODO: we could use isStrongerThan for further minimization
				// using a LinkedHashSet to keep the ordering that aligns edge labels and their version that includes
				//   the ground partial arrangement..

				// also: filter out "false" elements, and do absorption through "true"

				final List<CongruenceClosure<NODE, FUNCTION>> newPasForDimension = new ArrayList<>();
				final List<CongruenceClosure<NODE, FUNCTION>> newPasWgpaForDimension = new ArrayList<>();
				for (int i = 0; i < this.mLabel.size(); i++) {
					final CongruenceClosure<NODE, FUNCTION> currentLabel = this.mLabel.get(i);
					if (currentLabel.isTautological()) {
						return new WeakEquivalenceEdgeLabel();
					}
					if (currentLabel.isInconsistent()) {
						// filter out the "false"
						continue;
					}
					newPasForDimension.add(this.mLabel.get(i));
					newPasWgpaForDimension.add(this.mLabelWithGroundPa.get(i));
				}

				for (int i = 0; i < other.mLabel.size(); i++) {
					final CongruenceClosure<NODE, FUNCTION> currentLabel = other.mLabel.get(i);
					if (currentLabel.isTautological()) {
						return new WeakEquivalenceEdgeLabel();
					}
					if (currentLabel.isInconsistent()) {
						// filter out the "false"
						continue;
					}
					newPasForDimension.add(other.mLabel.get(i));
					newPasWgpaForDimension.add(other.mLabelWithGroundPa.get(i));
				}

//				newPasForDimension.addAll(this.mLabel);
//				newPasForDimension.addAll(other.mLabel);
//				newPasWgpaForDimension.addAll(this.mLabelWithGroundPa);
//				newPasWgpaForDimension.addAll(other.mLabelWithGroundPa);

//				return new WeakEquivalenceEdgeLabel(new ArrayList<>(newPasForDimension), mArityOfArrays);
				return new WeakEquivalenceEdgeLabel(newPasForDimension, newPasWgpaForDimension);
//				return new WeakEquivalenceEdgeLabel(new ArrayList<>(newPasForDimension),
//						new ArrayList<>(newPasWgpaForDimension));
			}


			/**
			 *  <li> compute the meet with the ground partial arrangement
			 *  <li> project out the variable to be projected elem
			 *  <li> project out all constraints that do not contain a weq-variable
			 *
			 * @param elem
			 * @param groundPartialArrangement
			 */
			public void projectElement(final NODE elem,
					final CongruenceClosure<NODE, FUNCTION> groundPartialArrangement) {
				projectHelper(cc -> cc.removeElement(elem), groundPartialArrangement);
//				for (int i = 0; i < mLabel.size(); i++) {
//					final CongruenceClosure<NODE, FUNCTION> meet = mLabel.get(i).meet(groundPartialArrangement);
//					meet.removeElement(elem);
//					final CongruenceClosure<NODE, FUNCTION> newPa = meet.projectToElements(mFactory.getAllWeqNodes());
//					mLabel.set(i, newPa);
//				}
				assert sanityCheckAfterProject(elem, groundPartialArrangement);
			}

			public void projectFunction(final FUNCTION func,
					final CongruenceClosure<NODE, FUNCTION> groundPartialArrangement) {
				projectHelper(cc -> cc.removeFunction(func), groundPartialArrangement);
//				assert sanityCheck();
				assert sanityCheckAfterProject(func, groundPartialArrangement);
			}


			private void projectHelper(final Consumer<CongruenceClosure<NODE, FUNCTION>> remove,
					final CongruenceClosure<NODE, FUNCTION> groundPartialArrangement) {
				for (int i = 0; i < mLabel.size(); i++) {
					final CongruenceClosure<NODE, FUNCTION> meet = mLabel.get(i).meet(groundPartialArrangement);
					remove.accept(meet);
					mLabelWithGroundPa.set(i, meet);
					final CongruenceClosure<NODE, FUNCTION> newPa = meet.projectToElements(mFactory.getAllWeqNodes());
					mLabel.set(i, newPa);
				}
			}


			@Override
			public String toString() {
				return mLabel.toString();
			}

			private boolean sanityCheck() {
				return sanityCheck(mPartialArrangement);
			}

			private boolean sanityCheck(final CongruenceClosure<NODE, FUNCTION> groundPartialArrangement) {
				if (mLabel.size() != mLabelWithGroundPa.size()) {
					assert false;
					return false;
				}

				if (groundPartialArrangement != null) {
					for (int i = 0; i < mLabel.size(); i++) {
						final CongruenceClosure<NODE, FUNCTION> labelGpaMeet =
								mLabel.get(i).meet(groundPartialArrangement);
						if (!labelGpaMeet.isEquivalent(mLabelWithGroundPa.get(i))) {
							assert false;
							return false;
						}
					}
				}

				if (mLabel.stream().anyMatch(pa -> pa.isTautological()) && mLabel.size() != 1) {
					assert false : "missing normalization: if there is one 'true' disjunct, we can drop"
							+ "all other disjuncts";
					return false;
				}

				if (mLabel.stream().anyMatch(pa -> pa.isInconsistent())) {
					assert false : "missing normalization: contains 'false' disjuncts";
					return false;
				}

				return true;
			}

			private boolean sanityCheckAfterProject(final FUNCTION func,
					final CongruenceClosure<NODE, FUNCTION> groundPartialArrangement) {
				final CongruenceClosure<NODE, FUNCTION> copy = new CongruenceClosure<>(groundPartialArrangement);
				copy.removeFunction(func);
				return sanityCheck(copy);

			}

			/**
			 * special sanity check where we check as normal except that we are checkin wrt another gpa, not mPartial..
			 * but mPartial.. where elem has been projected out (as this will be done after the project in the weq
			 * labels)
			 *
			 * @param elem
			 * @param groundPartialArrangement
			 * @return
			 */
			private boolean sanityCheckAfterProject(final NODE elem,
					final CongruenceClosure<NODE, FUNCTION> groundPartialArrangement) {
				final CongruenceClosure<NODE, FUNCTION> copy = new CongruenceClosure<>(groundPartialArrangement);
				copy.removeElement(elem);
				return sanityCheck(copy);
			}
		}

		public  Map<FUNCTION, WeakEquivalenceEdgeLabel> getAdjacentWeqEdges(final FUNCTION appliedFunction) {
			final Map<FUNCTION, WeakEquivalenceEdgeLabel> result = new HashMap<>();
			for (final Entry<Doubleton<FUNCTION>, WeakEquivalenceEdgeLabel> en : mWeakEquivalenceEdges.entrySet()) {
				if (en.getKey().getOneElement().equals(appliedFunction)) {
					result.put(en.getKey().getOtherElement(), en.getValue());
				}
				if (en.getKey().getOtherElement().equals(appliedFunction)) {
					result.put(en.getKey().getOneElement(), en.getValue());
				}
			}
			return result;
		}

	}