package de.uni_freiburg.informatik.ultimate.modelcheckerutils.absint.vpdomain;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.function.BiPredicate;
import java.util.function.Function;
import java.util.function.Predicate;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.CcManager;
import de.uni_freiburg.informatik.ultimate.util.datastructures.CongruenceClosure;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ICongruenceClosure;
import de.uni_freiburg.informatik.ultimate.util.datastructures.RemoveCcElement;
import de.uni_freiburg.informatik.ultimate.util.datastructures.poset.PartialOrderCache;

/**
 * Represents an edge label in the weak equivalence graph.
 * An edge label connects two arrays of the same arity(dimensionality) #a.
 * An edge label is a tuple of length #a.
 * Each tuple element is a set of partial arrangements. The free variables in the partial arrangements are the
 * variables of the EqConstraint together with #a special variables that are implicitly universally quantified
 * and range over the array positions.
 *
 */
class WeakEquivalenceEdgeLabel<NODE extends IEqNodeIdentifier<NODE>> {

	/**
	 *
	 */
	private final WeakEquivalenceGraph<NODE> mWeakEquivalenceGraph;
	final Set<CongruenceClosure<NODE>> mLabel;

	private final WeqCcManager<NODE> mWeqCcManager;

	/**
	 * Copy constructor.
	 *
	 * @param original
	 * @param weakEquivalenceGraph TODO
	 */
	public WeakEquivalenceEdgeLabel(final WeakEquivalenceGraph<NODE> weakEquivalenceGraph,
			final WeakEquivalenceEdgeLabel<NODE> original) {
		mWeakEquivalenceGraph = weakEquivalenceGraph;
		mWeqCcManager = weakEquivalenceGraph.getWeqCcManager();
		mLabel = new HashSet<>(original.getLabelContents().size());
		for (final CongruenceClosure<NODE> l : original.getLabelContents()) {
			assert !l.isInconsistent();
			assert !l.isTautological() || original.getLabelContents().size() == 1;
			mLabel.add(new CongruenceClosure<>(l));
		}
		assert sanityCheck();
	}

	/**
	 * Construct a weak equivalence edge from a list of label contents.
	 *
	 * Does some simplifications.
	 *
	 * @param newLabelContents
	 * @param weakEquivalenceGraph TODO
	 */
	public WeakEquivalenceEdgeLabel(final WeakEquivalenceGraph<NODE> weakEquivalenceGraph,
			final Set<CongruenceClosure<NODE>> newLabelContents) {
		mWeakEquivalenceGraph = weakEquivalenceGraph;
		mWeqCcManager = weakEquivalenceGraph.getWeqCcManager();
		mLabel = mWeqCcManager.filterRedundantCcs(newLabelContents);
		if (mLabel.size() == 1 && mLabel.iterator().next().isInconsistent()) {
			//case mLabel = "[False]" -- filterRedundantCcs leaves this case so we have to clean up manually to "[]"
			mLabel.clear();
		}
		assert sanityCheck();
	}

	/**
	 * Constructs an empty edge. (labeled "true")
	 * @param weakEquivalenceGraph TODO
	 */
	public WeakEquivalenceEdgeLabel(final WeakEquivalenceGraph<NODE> weakEquivalenceGraph) {
		mWeakEquivalenceGraph = weakEquivalenceGraph;
		mWeqCcManager = weakEquivalenceGraph.getWeqCcManager();
		mLabel = new HashSet<>();
		mLabel.add(new CongruenceClosure<>(mWeakEquivalenceGraph.getLogger()));
		assert sanityCheck();
	}

	/**
	 *
	 * @return a copy of this weq edge where all disjuncts have been joined into one
	 */
	public WeakEquivalenceEdgeLabel<NODE> flatten(final WeakEquivalenceGraph<NODE> weqGraphForFlattenedLabel) {
		if (isInconsistent()) {
			return this;
		}
		return new WeakEquivalenceEdgeLabel<NODE>(weqGraphForFlattenedLabel, Collections.singleton(
				mLabel.stream().reduce((cc1, cc2) -> cc1.join(cc1)).get()));
	}

	public void setExternalRemInfo(final RemoveCcElement<NODE> remInfo) {
		for (final CongruenceClosure<NODE> lab : mLabel) {
			lab.setExternalRemInfo(remInfo);
		}
	}

	public boolean hasExternalRemInfo() {
		for (final CongruenceClosure<NODE> l : mLabel) {
			assert l.assertHasExternalRemInfo();
		}
		return true;
	}

	public boolean assertHasOnlyWeqVarConstraints(final Set<NODE> weqVarsForThisEdge) {
		for (final CongruenceClosure<NODE> l : mLabel) {
			if (!l.assertHasOnlyWeqVarConstraints(weqVarsForThisEdge)) {
				assert false;
				return false;
			}
		}
		return true;
	}

	public void projectWeqVarNode(final NODE firstDimWeqVarNode) {
		for (final CongruenceClosure<NODE> lab : mLabel) {
//			lab.removeSimpleElementDontIntroduceNewNodes(firstDimWeqVarNode);
			RemoveCcElement.removeSimpleElementDontIntroduceNewNodes(lab, firstDimWeqVarNode);
		}
		assert sanityCheckDontEnforceProjectToWeqVars(mWeakEquivalenceGraph.mPartialArrangement);
	}

	public Set<NODE> projectSimpleElement(final NODE elem, final boolean useWeqGpaMode) {
		if (isTautological()) {
			return Collections.emptySet();
		}
		if (isInconsistent()) {
			return Collections.emptySet();
		}

		final Set<NODE> nodesToAddToGpa = new HashSet<>();

		final List<CongruenceClosure<NODE>> newLabelContents = new ArrayList<>(mLabel.size());
		for (final CongruenceClosure<NODE> lab : mLabel) {
			assert lab.sanityCheckOnlyCc(mWeakEquivalenceGraph.mPartialArrangement.getElementCurrentlyBeingRemoved());

			/*
			 * just removing elem is not enough
			 * example:
			 *  elem = a
			 *  label has a[q]
			 *  then a[q] needs to be removed, but mPartialArrangement cannot know that..
			 *
			 *  actually, even removeSimpleElement is not enough, because we might be removing
			 *   a[i], a (in that order)
			 *   then during removing a[i] we add a node a[q], but dont insert a, because it is in remInfo
			 *   then when we remove a, the removeSimpleElement will just say the cc does not have a and do
			 *   nothing
			 *
			 *  plan: compute all dependents, and remove them one by one
			 */
			if (useWeqGpaMode) {
				/*
				 *  current label has been joined with WeqGpa
				 *  (i.e. lab is a WeqCongruenceClosure, not only a CongruenceClosure)
				 *  use CcGpa inside this remove.. (avoids endless recursion)
				 */
//				final Set<NODE> nodesAdded = lab.removeSimpleElementDontUseWeqGpaTrackAddedNodes(elem);
				final Set<NODE> nodesAdded = RemoveCcElement.removeSimpleElementDontUseWeqGpaTrackAddedNodes(lab, elem);
				// some nodes may have been introduced
				nodesAdded.stream()
				.filter(n -> !CongruenceClosure.dependsOnAny(n,
						mWeakEquivalenceGraph.getWeqCcManager().getAllWeqPrimedNodes()))
				.forEach(nodesToAddToGpa::add);
			} else {
				/*
				 * lightweight case, current label is a CongruenceClosure, not a WeqCongruenceClosure
				 * --> we do not allow introduction of new nodes during the remove operation in the labels here
				 */
//				lab.removeSimpleElementDontIntroduceNewNodes(elem);
				RemoveCcElement.removeSimpleElementDontIntroduceNewNodes(lab, elem);
			}

			assert lab.assertSingleElementIsFullyRemoved(elem);

			if (lab.isTautological()) {
				// a disjunct became "true" through projection --> the whole disjunction is tautological
				mLabel.clear();
				mLabel.add(new CongruenceClosure<>(mWeakEquivalenceGraph.getLogger()));
				return Collections.emptySet();
			}
			assert lab.sanityCheckOnlyCc(mWeakEquivalenceGraph.mPartialArrangement.getElementCurrentlyBeingRemoved());

			final CongruenceClosure<NODE> lab2;
			if (useWeqGpaMode) {
				// unprime weqvars
				lab2 = new CongruenceClosure<>(lab);
				lab2.transformElementsAndFunctions(
						node -> node.renameVariables(mWeakEquivalenceGraph.getWeqCcManager().getWeqPrimedVarsToWeqVars()));
			} else {
				lab2 = lab;
			}

			final CongruenceClosure<NODE> newLab = lab2.projectToElements(mWeakEquivalenceGraph.getWeqCcManager().getAllWeqNodes(),
					mWeakEquivalenceGraph.mPartialArrangement.getElementCurrentlyBeingRemoved());
			assert newLab.assertSingleElementIsFullyRemoved(elem);
			assert !newLab.isTautological();
			assert newLab.sanityCheckOnlyCc(mWeakEquivalenceGraph.mPartialArrangement.getElementCurrentlyBeingRemoved());
			newLabelContents.add(newLab);
		}
		mLabel.clear();
		mLabel.addAll(newLabelContents);
		assert mLabel.stream().allMatch(l -> l.assertSingleElementIsFullyRemoved(elem));
		assert sanityCheck();
		return nodesToAddToGpa;
	}

	public WeakEquivalenceEdgeLabel<NODE> projectToElements(final Set<NODE> allWeqNodes) {
		if (isInconsistent()) {
			return this;
		}
		final Set<CongruenceClosure<NODE>> newLabelContents = new HashSet<>();
		for (final CongruenceClosure<NODE> item : mLabel) {
			newLabelContents.add(item.projectToElements(allWeqNodes,
					mWeakEquivalenceGraph.mPartialArrangement.getElementCurrentlyBeingRemoved()));
		}
		assert newLabelContents.stream().allMatch(l -> l.sanityCheckOnlyCc());
		final WeakEquivalenceEdgeLabel<NODE> result =
				new WeakEquivalenceEdgeLabel<NODE>(mWeakEquivalenceGraph, newLabelContents);
		assert result.sanityCheck();
		return result;
	}

	/**
	 *
	 *
	 * @param inOrDecrease how much to shift (negative value for decrease)
	 * @param weqVarsForThisEdge this edgeLabel does not know the function signature of its source and target;
	 *     thus we pass a list of weqVars that belongs to that signature (those are the ones to be shifted..)
	 *     they must be in correct order of dimensions according to source/target
	 */
	public void inOrDecreaseWeqVarIndices(final int inOrDecrease, final List<NODE> weqVarsForThisEdge) {
		assert inOrDecrease == 1 || inOrDecrease == -1 : "we don't expect any other cases";
		assert inOrDecrease != 1 || !this.getAppearingNodes()
				.contains(weqVarsForThisEdge.get(weqVarsForThisEdge.size() - 1)) : "project the highest weqvar "
				+ "before increasing!";
				assert inOrDecrease != -1 || !this.getAppearingNodes()
						.contains(weqVarsForThisEdge.get(0)) : "project the lowest weqvar before decreasing!";

						final Map<Term, Term> substitutionMapping = new HashMap<>();
						for (int i = 0; i < weqVarsForThisEdge.size(); i++) {
							final NODE nodeI = weqVarsForThisEdge.get(i);
							final int newDim = i + inOrDecrease;
							// the others (newDim <0) should have been projected out of the formula before.. (in the calling method)
							if (newDim >= 0 && newDim < weqVarsForThisEdge.size()) {
								substitutionMapping.put(nodeI.getTerm(),
										mWeakEquivalenceGraph.getWeqCcManager().getWeqVariableForDimension(newDim, nodeI.getSort()));
							}
						}
						this.transformElements(e -> e.renameVariables(substitutionMapping));
						assert sanityCheckDontEnforceProjectToWeqVars(mWeakEquivalenceGraph.mPartialArrangement);
	}

	public boolean isConstrained(final NODE elem) {
		return mLabel.stream().anyMatch(l -> l.isConstrained(elem));
	}

	public Set<CongruenceClosure<NODE>> getLabelContents() {
		return Collections.unmodifiableSet(mLabel);
	}

	public boolean isInconsistent() {
		for (final CongruenceClosure<NODE> pa : getLabelContents()) {
			if (!pa.isInconsistent()) {
				// we found one consistent disjunct --> this label is consistent
				return false;
			} else {
				// current cc is inconsistent
				assert getLabelContents().size() == 1 : "we are filtering out all but one 'bottoms', right?";
			}
		}
		return true;
	}

	/**
	 * Called when the ground partial arrangement (gpa) has changed.
	 * Checks if any entry of a weq label became inconsistent through the change, removes that entry, propagates
	 * an array equality if the whole edge became inconsistent
	 *
	 *  --> does edge inconsistency based propagations (weak equivalences becoming strong ones)
	 *  --> does not do congruence style weq propagations, those are done separately when an equality is added
	 *   to the gpa
	 *
	 * @param reportX lambda, applying one of the CongruenceClosure.report functions to some nodes for a given
	 *   CongruenceClosure object
	 * @return a fresh, updated WeqLabel, null if the label became inconsistent
	 */
	public WeakEquivalenceEdgeLabel<NODE> reportChangeInGroundPartialArrangement(
			final Predicate<CongruenceClosure<NODE>> reportX) {
		assert this.sanityCheck();


		final Set<CongruenceClosure<NODE>> newLabel = new HashSet<>();

		for (final CongruenceClosure<NODE> l : mLabel) {
			assert mWeakEquivalenceGraph.mPartialArrangement.sanityCheck();
			assert l.sanityCheckOnlyCc();
			final CongruenceClosure<NODE> currentPaWgpa = mWeqCcManager.meet(l,
					mWeakEquivalenceGraph.mPartialArrangement.getCongruenceClosure(),
					mWeakEquivalenceGraph.mPartialArrangement.getElementCurrentlyBeingRemoved());

			if (currentPaWgpa.isInconsistent()) {
				// label element became inconsistent, don't add it to the new label
				continue;
			}

			final boolean change = reportX.test(currentPaWgpa);

			if (!change) {
				/*
				 *  no change in mLabelWgpa[i] meet gpa -- this can happen, because labelWgpa might imply an
				 *  equality that is not present in gpa..
				 *
				 *  no checks need to be made here, anyway
				 */
				newLabel.add(l);
				assert !currentPaWgpa.isInconsistent();
				continue;
			}

			// add the strengthened version as the new label element
			newLabel.add(currentPaWgpa.projectToElements(mWeakEquivalenceGraph.getWeqCcManager().getAllWeqNodes(),
					mWeakEquivalenceGraph.mPartialArrangement.getElementCurrentlyBeingRemoved()));

			assert this.sanityCheck();
		}
		assert newLabel.stream().allMatch(CongruenceClosure::sanityCheckOnlyCc);
		return new WeakEquivalenceEdgeLabel<NODE>(mWeakEquivalenceGraph, newLabel);
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
		for (final CongruenceClosure<NODE> cc : mLabel) {
			final List<Term> cube = CcManager.congruenceClosureToCube(script, cc);
			final Term cubeTerm = SmtUtils.and(script, cube);
			result.add(cubeTerm);
		}
		return result;
	}

	public void transformElements(final Function<NODE, NODE> transformer) {
		assert sanityCheckDontEnforceProjectToWeqVars(mWeakEquivalenceGraph.mPartialArrangement);
		//			for (int i = 0; i < getLabelContents().size(); i++) {
		for (final CongruenceClosure<NODE> l : mLabel) {
			l.transformElementsAndFunctions(transformer);
			assert sanityCheckDontEnforceProjectToWeqVars(mWeakEquivalenceGraph.mPartialArrangement);
		}
		assert sanityCheckDontEnforceProjectToWeqVars(mWeakEquivalenceGraph.mPartialArrangement);
	}

	/**
	 * Returns all NODEs that are used in this WeqEdgeLabel.
	 * Not including the special quantified variable's nodes.
	 * @return
	 */
	public Set<NODE> getAppearingNodes() {
		final Set<NODE> res = new HashSet<>();
		getLabelContents().forEach(pa -> res.addAll(pa.getAllElements()));
		return res;
	}

	public WeakEquivalenceEdgeLabel<NODE> meet(final WeakEquivalenceEdgeLabel<NODE> otherLabel) {
		return meet(otherLabel.getLabelContents());
	}

	WeakEquivalenceEdgeLabel<NODE> meet(final Set<CongruenceClosure<NODE>> paList) {
		assert sanityCheckDontEnforceProjectToWeqVars(mWeakEquivalenceGraph.mPartialArrangement);
		return meetRec(paList);
	}

	WeakEquivalenceEdgeLabel<NODE> meetRec(final Set<CongruenceClosure<NODE>> paList) {
		final Set<CongruenceClosure<NODE>> newLabelContent = new HashSet<>();
		for (final CongruenceClosure<NODE> lc1 : mLabel) {
			for (final CongruenceClosure<NODE> lc2 : paList) {
				newLabelContent.add(lc1.meetRec(lc2));
			}
		}

		final Set<CongruenceClosure<NODE>> newLabel = mWeqCcManager.filterRedundantCcs(newLabelContent);
		assert newLabel.stream().allMatch(l -> l.sanityCheckOnlyCc());

		final Set<CongruenceClosure<NODE>> newLabelProjected = newLabel.stream()
				.map(l -> l.projectToElements(mWeakEquivalenceGraph.getWeqCcManager().getAllWeqNodes(),
						mWeakEquivalenceGraph.mPartialArrangement.getElementCurrentlyBeingRemoved())).collect(Collectors.toSet());
		assert newLabelProjected.stream()
		.allMatch(l -> l.sanityCheckOnlyCc(mWeakEquivalenceGraph.mPartialArrangement.getElementCurrentlyBeingRemoved()));

		final WeakEquivalenceEdgeLabel<NODE> result =
				new WeakEquivalenceEdgeLabel<NODE>(mWeakEquivalenceGraph, newLabelProjected);
		assert result.sanityCheck();
		return result;
	}

	/**
	 * rule:  A isStrongerThan B
	 *     iff
	 *   forall ai exists bi. ai subseteq bi
	 * @param ccPoCache
	 * @param value
	 * @return
	 */
	public boolean isStrongerThan(final WeakEquivalenceEdgeLabel<NODE> other) {
		return isStrongerThan(other, CongruenceClosure::isStrongerThan);
	}

	public boolean isStrongerThan(final WeakEquivalenceEdgeLabel<NODE> other,
			final BiPredicate<CongruenceClosure<NODE>, CongruenceClosure<NODE>> lowerOrEqual) {
		for (final CongruenceClosure<NODE> paThis : getLabelContents()) {
			boolean existsWeaker = false;
			for (final CongruenceClosure<NODE> paOther : other.getLabelContents()) {
				if (lowerOrEqual.test(paThis, paOther)) {
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
	 * @param ccPoCache
	 * @param correspondingWeqEdgeInOther
	 * @return
	 */
	public WeakEquivalenceEdgeLabel<NODE> union(final WeakEquivalenceEdgeLabel<NODE> other) {
		return this.union(other, null);
	}

	public WeakEquivalenceEdgeLabel<NODE> union(final WeakEquivalenceEdgeLabel<NODE> other,
			final PartialOrderCache<CongruenceClosure<NODE>> ccPoCache) {
		assert this.sanityCheck() && other.sanityCheck();
		//			assert this.mLabel.size() < 10 && other.mLabel.size() < 10;
		final List<CongruenceClosure<NODE>> unionList = new ArrayList<>(
				mLabel.size() + other.getLabelContents().size());
		unionList.addAll(mLabel);
		unionList.addAll(other.getLabelContents());

		final Set<CongruenceClosure<NODE>> filtered = ccPoCache == null ?
				mWeqCcManager.filterRedundantCcs(new HashSet<>(unionList))
				: mWeqCcManager.filterRedundantCcs(new HashSet<>(unionList), ccPoCache);

				final WeakEquivalenceEdgeLabel<NODE> result = new WeakEquivalenceEdgeLabel<>(mWeakEquivalenceGraph,
						filtered);
				assert result.sanityCheck();
				return result;
	}

	boolean isTautological() {
		for (final CongruenceClosure<NODE> l : getLabelContents()) {
			if (l.isTautological()) {
				assert getLabelContents().size() == 1;
				return true;
			}
		}
		return false;
	}


	@Override
	public String toString() {
		if (mLabel.size() < 3) {
			return toLogString();
		}
		return "weq edge label, size: " + mLabel.size();
	}

	public String toLogString() {
		if (isInconsistent()) {
			return "False";
		}
		if (isTautological()) {
			return "True";
		}


		final StringBuilder sb = new StringBuilder();

		mLabel.forEach(l -> sb.append(l.toLogString() + "\n"));
		return sb.toString();
	}

	boolean sanityCheck() {
		return sanityCheck(mWeakEquivalenceGraph.mPartialArrangement);
	}

	private boolean sanityCheck(final WeqCongruenceClosure<NODE> groundPartialArrangement) {
		if (mWeakEquivalenceGraph.getWeqCcManager() == null) {
			return true;
		}
		if (mWeakEquivalenceGraph.isEmpty()) {
			return true;
		}

		if (mLabel.stream().anyMatch(l -> l.isTautological()) && mLabel.size() > 1) {
			// not normalized
			assert false;
			return false;
		}

		if (mLabel.stream().anyMatch(l -> l.isInconsistent())) {
			// not normalized
			assert false;
			return false;
		}

		// check that labels are free of weqPrimed vars
		if (!groundPartialArrangement.mMeetWithGpaCase) {
			for (final CongruenceClosure<NODE> lab : mLabel) {
				for (final NODE el : lab.getAllElements()) {
					if (CongruenceClosure.dependsOnAny(el, mWeakEquivalenceGraph.getWeqCcManager().getAllWeqPrimedNodes())) {
						assert false;
						return false;
					}
				}
			}
		}

		// check that labels are free of constraints that don't contain weq nodes
		for (final CongruenceClosure<NODE> lab : mLabel) {
			assert lab.assertHasOnlyWeqVarConstraints(mWeakEquivalenceGraph.getWeqCcManager().getAllWeqNodes());
		}

		return sanityCheckDontEnforceProjectToWeqVars(mWeakEquivalenceGraph.mPartialArrangement);
	}

	public void meetWithWeqGpa(final WeqCongruenceClosure<NODE> originalPa) {

		final List<CongruenceClosure<NODE>> newLabelContents = new ArrayList<>();
		for (final CongruenceClosure<NODE> l : mLabel) {

			// make a copy of the full abstract state (ground partial arrangement and weak equivalence graph, weqCc)
			//				final WeqCongruenceClosure<NODE> paCopy = new WeqCongruenceClosure<>(originalPa, true);
			WeqCongruenceClosure<NODE> paCopy = mWeqCcManager.makeCopyForWeqMeet(originalPa);


			// make a copy of the label, prime the weq vars
			final CongruenceClosure<NODE> lCopy = new CongruenceClosure<>(l);
			lCopy.transformElementsAndFunctions(
					n -> n.renameVariables(mWeakEquivalenceGraph.getWeqCcManager().getWeqVarsToWeqPrimedVars()));

			// report all constraints from the label into the copy of the weqCc
			for (final Entry<NODE, NODE> eq : lCopy.getSupportingElementEqualities().entrySet()) {
				if (paCopy.isInconsistent()) {
//					mLabel.clear();
					break;
				}
//				paCopy.reportEquality(eq.getKey(), eq.getValue());
				paCopy = mWeqCcManager.reportEquality(paCopy, eq.getKey(), eq.getValue());
			}
			for (final Entry<NODE, NODE> deq : lCopy.getElementDisequalities().entrySet()) {
				if (paCopy.isInconsistent()) {
//					mLabel.clear();
					break;
				}
//				paCopy.reportDisequality(deq.getKey(), deq.getValue());
				paCopy = mWeqCcManager.reportDisequality(paCopy, deq.getKey(), deq.getValue());
			}

			if (paCopy.isTautological()) {
				mLabel.clear();
				mLabel.add(new CongruenceClosure<NODE>(mWeakEquivalenceGraph.getLogger()));
				return;
			}

			if (!paCopy.isInconsistent()) {
				newLabelContents.add(paCopy.getCongruenceClosure());
			}
		}

		mLabel.clear();
		mLabel.addAll(newLabelContents);

		assert sanityCheckDontEnforceProjectToWeqVars(mWeakEquivalenceGraph.mPartialArrangement);

	}

	public void meetWithCcGpa() {

		final Set<CongruenceClosure<NODE>> newLabelContents = new HashSet<>();
		//			for (int i = 0; i < getLabelContents().size(); i++) {
		for (final CongruenceClosure<NODE> l : mLabel) {
			if (l.isTautological()) {
				// we have one "true" disjunct --> the whole disjunction is tautological
				if (mLabel.size() == 1) {
					return;
				}
				mLabel.clear();
				mLabel.add(new CongruenceClosure<>(mWeakEquivalenceGraph.getLogger()));
				return;
			}
			final CongruenceClosure<NODE> meet;
//			if (meetWithFullWeqCc) {
//				meet = mWeakEquivalenceGraph.mCcManager.getWeqMeet(l, mWeakEquivalenceGraph.mPartialArrangement);
//			} else {
				meet = mWeqCcManager.meet(l,
						mWeakEquivalenceGraph.mPartialArrangement.getCongruenceClosure(),
						mWeakEquivalenceGraph.mPartialArrangement.getElementCurrentlyBeingRemoved());
//			}

			if (meet.isInconsistent()) {
				/* label element is inconsistent with the current gpa
				 * --> omit it from the new label
				 */
				continue;
			}
			if (meet.isTautological()) {
				assert false : "this should never happen because if the meet is tautological then mLabel.get(i)"
						+ "is, too, right?";
			// we have one "true" disjunct --> the whole disjunction is tautological
			mLabel.clear();
			mLabel.add(new CongruenceClosure<>(mWeakEquivalenceGraph.getLogger()));
			return;
			}
			newLabelContents.add(meet);
		}
		assert newLabelContents.size() <= 1 || !newLabelContents.stream().anyMatch(c -> c.isTautological());


		mLabel.clear();
		mLabel.addAll(newLabelContents);

		assert sanityCheckDontEnforceProjectToWeqVars(mWeakEquivalenceGraph.mPartialArrangement);
	}

	boolean sanityCheckDontEnforceProjectToWeqVars(final ICongruenceClosure<NODE> groundPartialArrangement) {
		for (final CongruenceClosure<NODE> lab : mLabel) {
			if (!lab.sanityCheckOnlyCc(groundPartialArrangement.getElementCurrentlyBeingRemoved())) {
				assert false;
				return false;
			}
		}

		// check label normalization
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

	public boolean assertElementIsFullyRemoved(final NODE elem) {
		for (final CongruenceClosure<NODE> lab : mLabel) {
			if (!lab.assertSingleElementIsFullyRemoved(elem)) {
				assert false;
				return false;
			}
		}
		return true;
	}

	public WeakEquivalenceGraph<NODE> getWeqGraph() {
		return mWeakEquivalenceGraph;
	}
}