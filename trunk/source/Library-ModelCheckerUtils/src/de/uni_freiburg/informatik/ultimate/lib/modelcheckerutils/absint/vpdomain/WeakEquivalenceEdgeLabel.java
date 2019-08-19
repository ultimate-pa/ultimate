/*
 * Copyright (C) 2017 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
 *
 * This file is part of the ULTIMATE AbstractInterpretationV2 plug-in.
 *
 * The ULTIMATE AbstractInterpretationV2 plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE AbstractInterpretationV2 plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE AbstractInterpretationV2 plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE AbstractInterpretationV2 plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE AbstractInterpretationV2 plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.vpdomain;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Function;
import java.util.function.Predicate;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.congruenceclosure.CongruenceClosure;
import de.uni_freiburg.informatik.ultimate.util.datastructures.congruenceclosure.IRemovalInfo;
import de.uni_freiburg.informatik.ultimate.util.datastructures.congruenceclosure.RemoveCcElement;
import de.uni_freiburg.informatik.ultimate.util.datastructures.congruenceclosure.SetConstraint;
import de.uni_freiburg.informatik.ultimate.util.datastructures.poset.PartialOrderCache;

/**
 * Represents an edge label in the weak equivalence graph.
 * An edge label connects two arrays of the same arity(dimensionality) #a.
 * An edge label is a tuple of length #a.
 * Each tuple element is a set of partial arrangements. The free variables in the partial arrangements are the
 * variables of the EqConstraint together with #a special variables that are implicitly universally quantified
 * and range over the array positions.
 *
 * @param <NODE> node in the weak equivalence graph
 *
 */
class WeakEquivalenceEdgeLabel<NODE extends IEqNodeIdentifier<NODE>> {

	private static final boolean MEET_IN_PLACE = true;

	private final WeakEquivalenceGraph<NODE> mWeakEquivalenceGraph;

	private final WeqCcManager<NODE> mWeqCcManager;

	private final Set<CongruenceClosure<NODE>> mDisjuncts;

	boolean mIsFrozen;


	/**
	 * Copy constructor.
	 *
	 * @param original
	 * @param weakEquivalenceGraph TODO
	 */
	WeakEquivalenceEdgeLabel(final WeakEquivalenceGraph<NODE> weakEquivalenceGraph,
			final WeakEquivalenceEdgeLabel<NODE> original,
			final boolean omitSanityCheck) {
		mWeakEquivalenceGraph = weakEquivalenceGraph;
		mWeqCcManager = weakEquivalenceGraph.getWeqCcManager();
		mDisjuncts = new HashSet<>(original.getNumberOfDisjuncts());
		for (final CongruenceClosure<NODE> l : original.getDisjuncts()) {
			assert !l.isInconsistent();
			assert !l.isTautological() || original.getDisjuncts().size() == 1;
			// if weqgraph is frozen, the weq labels must be frozen, too
			mDisjuncts.add(mWeqCcManager.copyCc(l, !mWeakEquivalenceGraph.isFrozen()));
		}
		assert !mWeakEquivalenceGraph.isFrozen() || mDisjuncts.stream().allMatch(cc -> cc.isFrozen());
		assert omitSanityCheck || sanityCheck();
	}

	/**
	 * Construct a weak equivalence edge from a list of label contents.
	 *
	 * Does some simplifications.
	 *
	 * @param newLabelContents
	 * @param weakEquivalenceGraph
	 */
	WeakEquivalenceEdgeLabel(final WeakEquivalenceGraph<NODE> weakEquivalenceGraph,
			final Set<CongruenceClosure<NODE>> newLabelContents) {
		this(weakEquivalenceGraph, newLabelContents, false);
	}

	/**
	 * Construct a weak equivalence edge from a list of label contents.
	 *
	 * Does some simplifications.
	 *
	 * @param newLabelContents
	 * @param weakEquivalenceGraph
	 */
	WeakEquivalenceEdgeLabel(final WeakEquivalenceGraph<NODE> weakEquivalenceGraph,
			final Set<CongruenceClosure<NODE>> newLabelContents, final boolean omitSanityChecks) {
		mWeakEquivalenceGraph = weakEquivalenceGraph;
		mWeqCcManager = weakEquivalenceGraph.getWeqCcManager();

		// TODO: this filter might be redundant because it is done outside every time (or the others are redundant..)
		mDisjuncts = mWeqCcManager.filterRedundantCcs(newLabelContents);

		if (mDisjuncts.size() == 1 && mDisjuncts.iterator().next().isInconsistent()) {
			//case mLabel = "[False]" -- filterRedundantCcs leaves this case so we have to clean up manually to "[]"
			mDisjuncts.clear();
		}
		assert mDisjuncts.stream().allMatch(cc -> !mWeakEquivalenceGraph.isFrozen() || cc.isFrozen());
		assert omitSanityChecks || sanityCheck();
	}

	/**
	 * Constructs an empty edge. (labeled "true")
	 * @param weakEquivalenceGraph TODO
	 */
	WeakEquivalenceEdgeLabel(final WeakEquivalenceGraph<NODE> weakEquivalenceGraph,
			final CongruenceClosure<NODE> emptyDisjunct) {
		mWeakEquivalenceGraph = weakEquivalenceGraph;
		mWeqCcManager = weakEquivalenceGraph.getWeqCcManager();
		mDisjuncts = new HashSet<>();
		if (weakEquivalenceGraph.isFrozen()) {
			mWeqCcManager.freezeIfNecessary(emptyDisjunct);
			mDisjuncts.add(emptyDisjunct);
		} else {
			mDisjuncts.add(mWeqCcManager.getCcManager().unfreezeIfNecessary(emptyDisjunct));
		}
		assert sanityCheck();
	}

	void setExternalRemInfo(final IRemovalInfo<NODE> remInfo) {
		for (final CongruenceClosure<NODE> lab : getDisjuncts()) {
			lab.setExternalRemInfo(remInfo);
		}
	}

	boolean hasExternalRemInfo() {
		for (final CongruenceClosure<NODE> l : getDisjuncts()) {
			assert l.assertHasExternalRemInfo();
		}
		return true;
	}

	boolean assertHasOnlyWeqVarConstraints(final Set<NODE> weqVarsForThisEdge) {
		for (final CongruenceClosure<NODE> l : getDisjuncts()) {
			if (!l.assertHasOnlyWeqVarConstraints(weqVarsForThisEdge)) {
				assert false;
				return false;
			}
		}
		return true;
	}

	void projectWeqVarNode(final NODE firstDimWeqVarNode) {
		for (final CongruenceClosure<NODE> lab : getDisjuncts()) {
			if (lab instanceof CongruenceClosure<?>) {
				RemoveCcElement.removeSimpleElementDontIntroduceNewNodes(lab, firstDimWeqVarNode);
			} else {
				throw new AssertionError("implement this?");
			}
		}
		assert sanityCheckDontEnforceProjectToWeqVars(mWeakEquivalenceGraph.mWeqCc);
	}

	/**
	 * (operates in place)
	 *
	 * @param elemToRemove
	 * @param useWeqGpaMode
	 * @return a set containing all nodes that have been added to the label's Ccs during execution of this method
	 */
	Set<NODE> projectAwaySimpleElement(final NODE elemToRemove) {
		if (isTautological()) {
			return Collections.emptySet();
		}
		if (isInconsistent()) {
			return Collections.emptySet();
		}

		final Set<NODE> nodesToAddToGpa = new HashSet<>();

		final List<CongruenceClosure<NODE>> newLabelContents = new ArrayList<>(getNumberOfDisjuncts());
		for (final CongruenceClosure<NODE> lab : getDisjuncts()) {
			assert lab.sanityCheckOnlyCc(mWeakEquivalenceGraph.mWeqCc.getElementCurrentlyBeingRemoved());

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
			 *  old plan: compute all dependents, and remove them one by one
			 *  current plan: do removeSimpleElement, but take care that no wrong nodes are added
			 */
//			if (mWeakEquivalenceGraph.mEmptyDisjunct instanceof WeqCongruenceClosure<?>) {
//				/*
//				 *  current label has been joined with WeqGpa
//				 *  (i.e. lab is a WeqCongruenceClosure, not only a CongruenceClosure)
//				 *  use CcGpa inside this remove.. (avoids endless recursion)
//				 */
//				final Set<NODE> nodesAdded = RemoveWeqCcElement.removeSimpleElementDontUseWeqGpaTrackAddedNodes(
//						(WeqCongruenceClosure<NODE>) lab, elemToRemove);
//				// some nodes may have been introduced
//				for (final NODE an : nodesAdded) {
//					if (!CongruenceClosure.dependsOnAny(an,
//							mWeakEquivalenceGraph.getWeqCcManager().getAllWeqPrimedNodes())) {
//						nodesToAddToGpa.add(an);
//					}
//				}
//			} else {
				/*
				 * lightweight case, current label is a CongruenceClosure, not a WeqCongruenceClosure
				 * --> we do not allow introduction of new nodes during the remove operation in the labels here
				 */
				RemoveCcElement.removeSimpleElementDontIntroduceNewNodes(lab, elemToRemove);
//			}

			assert lab.assertSingleElementIsFullyRemoved(elemToRemove);

			if (lab.isTautological()) {
				// a disjunct became "true" through projection --> the whole disjunction is tautological
//				setToTrue(mWeqCcManager.getEmptyIcc(lab, false));
				setToTrue(mWeqCcManager.getEmptyCc(false));
				return Collections.emptySet();
			}
			assert lab.sanityCheckOnlyCc(mWeakEquivalenceGraph.mWeqCc.getElementCurrentlyBeingRemoved());

			assert lab.assertSingleElementIsFullyRemoved(elemToRemove);
			assert !lab.isTautological();
			assert lab.sanityCheckOnlyCc(mWeakEquivalenceGraph.mWeqCc.getElementCurrentlyBeingRemoved());
			newLabelContents.add(lab);
		}
		setNewLabelContents(newLabelContents);
		assert getDisjuncts().stream().allMatch(l -> l.assertSingleElementIsFullyRemoved(elemToRemove));
		assert sanityCheck();
		return nodesToAddToGpa;
	}

	private int getNumberOfDisjuncts() {
		return mDisjuncts.size();
	}

	WeakEquivalenceEdgeLabel<NODE> projectToElements(final Set<NODE> allWeqNodes, final boolean  modifiable) {
		assert mWeakEquivalenceGraph.mWeqCc.mDiet == Diet.THIN
				// we allow thin-to fat here for the case when during fatten, a weq is reported during meetWWeqGpa
//				|| mWeakEquivalenceGraph.mWeqCc.mDiet == Diet.TRANSITORY_THIN_TO_WEQCCFAT
				;
		if (isInconsistent()) {
			return this;
		}
		if (allWeqNodes.isEmpty()) {
			return this;
		}
		final Set<CongruenceClosure<NODE>> newLabelContents = new HashSet<>();
		for (final CongruenceClosure<NODE> item : getDisjuncts()) {
			final CongruenceClosure<NODE> projected = mWeqCcManager.projectToElements(item, allWeqNodes,
					mWeakEquivalenceGraph.mWeqCc.getElementCurrentlyBeingRemoved(), modifiable);
			newLabelContents.add(projected);
		}
		assert newLabelContents.stream().allMatch(l -> l.sanityCheckOnlyCc());
		final WeakEquivalenceEdgeLabel<NODE> result =
				new WeakEquivalenceEdgeLabel<>(mWeakEquivalenceGraph, newLabelContents);
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
	void inOrDecreaseWeqVarIndices(final int inOrDecrease, final List<NODE> weqVarsForThisEdge) {
		assert inOrDecrease == 1 || inOrDecrease == -1 : "we don't expect any other cases";
		assert inOrDecrease != 1 || !this.getAppearingNodes().contains(weqVarsForThisEdge.get(
				weqVarsForThisEdge.size() - 1)) : "project the highest weqvar before increasing!";
		assert inOrDecrease != -1 || !this.getAppearingNodes().contains(weqVarsForThisEdge.get(0)) :
			"project the lowest weqvar before decreasing!";

		if (isTautological() || isInconsistent()) {
			return;
		}

		final Map<Term, Term> substitutionMapping = new HashMap<>();
		for (int i = 0; i < weqVarsForThisEdge.size(); i++) {
			final NODE nodeI = weqVarsForThisEdge.get(i);
			final int newDim = i + inOrDecrease;
			// the others (newDim <0) should have been projected out of the formula before.. (in the calling method)
			if (newDim >= 0 && newDim < weqVarsForThisEdge.size()) {
				substitutionMapping.put(nodeI.getTerm(),
						mWeqCcManager.getWeqVariableForDimension(newDim, nodeI.getSort()));
			}
		}
		this.transformElements(e -> e.renameVariables(substitutionMapping));
		assert sanityCheckDontEnforceProjectToWeqVars(mWeakEquivalenceGraph.mWeqCc);
	}

	boolean isConstrained(final NODE elem) {
		return getDisjuncts().stream().anyMatch(l -> l.isConstrained(elem));
	}

	Set<CongruenceClosure<NODE>> getDisjuncts() {
		return Collections.unmodifiableSet(mDisjuncts);
	}

	boolean isInconsistent() {
		for (final CongruenceClosure<NODE> pa : getDisjuncts()) {
			if (!pa.isInconsistent()) {
				// we found one consistent disjunct --> this label is consistent
				return false;
			} else {
				// current cc is inconsistent
				assert getDisjuncts().size() == 1 : "we are filtering out all but one 'bottoms', right?";
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
	@Deprecated
	WeakEquivalenceEdgeLabel<NODE> reportChangeInGroundPartialArrangement(
			final Predicate<CongruenceClosure<NODE>> reportX) {
		assert this.sanityCheck();

		final Set<CongruenceClosure<NODE>> newLabel = new HashSet<>();

		for (final CongruenceClosure<NODE> disjunct : getDisjuncts()) {
			assert mWeakEquivalenceGraph.mWeqCc.sanityCheck();
			assert disjunct.sanityCheckOnlyCc();

			final CongruenceClosure<NODE> meetWgpa;
			if (mWeqCcManager.getSettings().isMeetWithGpaOnReportchange()) {
				meetWgpa =  mWeqCcManager.meet(disjunct,
					mWeakEquivalenceGraph.mWeqCc.getCongruenceClosure(),
					mWeakEquivalenceGraph.mWeqCc.getElementCurrentlyBeingRemoved(),
					false);
			} else {
				meetWgpa = disjunct;
			}

			if (meetWgpa.isInconsistent()) {
				// label element became inconsistent, don't add it to the new label
				continue;
			}

			final boolean change = reportX.test(meetWgpa);

			if (!change) {
				/*
				 *  no change in mLabelWgpa[i] meet gpa -- this can happen, because labelWgpa might imply an
				 *  equality that is not present in gpa..
				 *
				 *  no checks need to be made here, anyway
				 */
				newLabel.add(disjunct);
				assert !meetWgpa.isInconsistent();
				continue;
			}

			if (mWeqCcManager.getSettings().isMeetWithGpaOnReportchange()) {
				// add the strengthened version as the new label element
				final CongruenceClosure<NODE> projected = mWeqCcManager.projectToElements(meetWgpa,
						mWeakEquivalenceGraph.getWeqCcManager().getAllWeqNodes(),
						mWeakEquivalenceGraph.mWeqCc.getElementCurrentlyBeingRemoved(),
						true);
				newLabel.add(projected);
			} else {
				newLabel.add(meetWgpa);
			}

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
	List<Term> toDnf(final Script script) {
		final List<Term> result = new ArrayList<>();
		for (final CongruenceClosure<NODE> d : getDisjuncts()) {
			final CongruenceClosure<NODE> cc = d;
			final List<Term> cube = CongruenceClosureSmtUtils.congruenceClosureToCube(script, cc,
					mWeqCcManager.getNonTheoryLiteralDisequalitiesIfNecessary());
			final Term cubeTerm = SmtUtils.and(script, cube);
			result.add(cubeTerm);
		}
		return result;
	}

	void transformElements(final Function<NODE, NODE> transformer) {
		assert !isFrozen();
		assert sanityCheckDontEnforceProjectToWeqVars(mWeakEquivalenceGraph.mWeqCc);

		final Collection<CongruenceClosure<NODE>> newLabelContents = new HashSet<>();
		for (final CongruenceClosure<NODE> l : getDisjuncts()) {
			if (l.isFrozen()) {
				final CongruenceClosure<NODE> unfrozen = mWeqCcManager.getCcManager().unfreeze(l);
				unfrozen.transformElementsAndFunctions(transformer);
				newLabelContents.add(unfrozen);
			} else {
				l.transformElementsAndFunctions(transformer);
				newLabelContents.add(l);
			}
			assert sanityCheckDontEnforceProjectToWeqVars(mWeakEquivalenceGraph.mWeqCc);
		}
		this.setNewLabelContents(newLabelContents);
		assert sanityCheckDontEnforceProjectToWeqVars(mWeakEquivalenceGraph.mWeqCc);
	}

	/**
	 * Returns all NODEs that are used in this WeqEdgeLabel.
	 * Not including the special quantified variable's nodes.
	 * @return
	 */
	Set<NODE> getAppearingNodes() {
		final Set<NODE> res = new HashSet<>();
		getDisjuncts().forEach(pa -> res.addAll(pa.getAllElements()));
		return res;
	}

	WeakEquivalenceEdgeLabel<NODE> meet(final WeakEquivalenceEdgeLabel<NODE> otherLabel,
			final boolean inplace) {
		assert sanityCheckDontEnforceProjectToWeqVars(mWeakEquivalenceGraph.mWeqCc);
		assert !inplace || !isFrozen();

		WeakEquivalenceEdgeLabel<NODE> originalThis = null;
		if (mWeqCcManager.areAssertsEnabled() && inplace) {
			originalThis = mWeqCcManager.copy(this, true, true);
		} else if (mWeqCcManager.areAssertsEnabled() && !inplace) {
			originalThis = this;
		}

		final Set<CongruenceClosure<NODE>> newLabelContent = new HashSet<>();
		for (final CongruenceClosure<NODE> lc1 : getDisjuncts()) {
			for (final CongruenceClosure<NODE> lc2 : otherLabel.getDisjuncts()) {
				if (inplace && !lc1.isFrozen()) {
					mWeqCcManager.meet(lc1, lc2, true);
					newLabelContent.add(lc1);
				} else {
					final CongruenceClosure<NODE> meet = mWeqCcManager.meet(lc1, lc2, false);
					newLabelContent.add(meet);
				}
			}
		}


		// need to do this before the project operation, as the projectToElements may violate the equivalence property
		assert mWeqCcManager.checkMeetWeqLabels(originalThis, otherLabel,
				new WeakEquivalenceEdgeLabel<NODE>(mWeakEquivalenceGraph, newLabelContent, true));

		final WeakEquivalenceEdgeLabel<NODE> result;
		if (inplace) {
			final Set<CongruenceClosure<NODE>> newLabelContentsFiltered =
					mWeqCcManager.filterRedundantCcs(newLabelContent);
			assert newLabelContentsFiltered.stream().allMatch(l -> l.sanityCheckOnlyCc());
			setNewLabelContents(newLabelContentsFiltered);
			result = this;
		} else {
			result = new WeakEquivalenceEdgeLabel<NODE>(mWeakEquivalenceGraph, newLabelContent);
		}
		if (!inplace) {
			result.freeze();
		}
		assert result.sanityCheck();
		return result;
	}

	/**
	 * Computes a constraint which, for every dimension, has the union of the disjuncts of both input labels
	 *  (this and other).
	 * @param ccPoCache
	 * @param correspondingWeqEdgeInOther
	 * @return
	 */
	WeakEquivalenceEdgeLabel<NODE> union(final WeakEquivalenceEdgeLabel<NODE> other) {
		return this.union(other, null);
	}

	WeakEquivalenceEdgeLabel<NODE> union(final WeakEquivalenceEdgeLabel<NODE> other,
			final PartialOrderCache<CongruenceClosure<NODE>> ccPoCache) {
		assert this.sanityCheck() && other.sanityCheck();
		if (this.isTautological()) {
			return this;
		}
		if (other.isTautological()) {
			return other;
		}
		if (this.isInconsistent()) {
			return other;
		}
		if (other.isInconsistent()) {
			return this;
		}


		final List<CongruenceClosure<NODE>> unionList = new ArrayList<>(getNumberOfDisjuncts()
				+ other.getNumberOfDisjuncts());
		unionList.addAll(this.getDisjuncts());
		unionList.addAll(other.getDisjuncts());

		final Set<CongruenceClosure<NODE>> filtered = ccPoCache == null ?
				mWeqCcManager.filterRedundantCcs(new HashSet<>(unionList)) :
					mWeqCcManager.filterRedundantCcs(new HashSet<>(unionList), ccPoCache);

		final WeakEquivalenceEdgeLabel<NODE> result = new WeakEquivalenceEdgeLabel<>(
					mWeakEquivalenceGraph, filtered);

		assert mWeqCcManager.getSettings().omitSanitycheckFineGrained2()
			|| assertUnionIntroducesNoNewNodes(this, other, result)
						: "union of two labels may not introduce any new nodes";

		assert result.sanityCheck();
		return result;
	}

	public static <NODE extends IEqNodeIdentifier<NODE>>
		boolean assertUnionIntroducesNoNewNodes(
				final WeakEquivalenceEdgeLabel<NODE> first,
				final WeakEquivalenceEdgeLabel<NODE> second,
			final WeakEquivalenceEdgeLabel<NODE> result) {
		final Set<NODE> difference = DataStructureUtils.difference(
				result.getAppearingNodes(),
				DataStructureUtils.union(first.getAppearingNodes(), second.getAppearingNodes()));
		if (!difference.isEmpty()) {
			assert false;
			return false;
		}
		return true;
	}

	boolean isTautological() {
		for (final CongruenceClosure<NODE> l : getDisjuncts()) {
			if (l.isTautological()) {
				assert getDisjuncts().size() == 1;
				return true;
			}
		}
		return false;
	}


	@Override
	public String toString() {
		if (getNumberOfDisjuncts() < mWeqCcManager.getSettings().getMaxNoEdgelabeldisjunctsForVerboseToString()) {
			return toLogString();
		}
		return "weq edge label, size: " + mDisjuncts.size();
	}

	public String toLogString() {
		if (isInconsistent()) {
			return "False";
		}
		if (isTautological()) {
			return "True";
		}


		final StringBuilder sb = new StringBuilder();

		getDisjuncts().forEach(l -> sb.append(l.toLogString() + "\n"));
		return sb.toString();
	}

	boolean sanityCheck() {
		return sanityCheck(mWeakEquivalenceGraph.mWeqCc);
	}

	private boolean sanityCheck(final WeqCongruenceClosure<NODE> baseWeqCc) {
		if (mWeakEquivalenceGraph.getWeqCcManager() == null) {
			return true;
		}

		if (getDisjuncts().stream().anyMatch(l -> l.isTautological()) && getDisjuncts().size() > 1) {
			// not normalized
			assert false;
			return false;
		}

		if (getDisjuncts().stream().anyMatch(l -> l.isInconsistent())) {
			// not normalized
			assert false;
			return false;
		}

		// check that labels are free of weqPrimed vars
		if (baseWeqCc != null
//				&& !baseWeqCc.isWeqFatEdgeLabel()
//		        && baseWeqCc.mDiet != Diet.WEQCCFAT
//				&& baseWeqCc.mDiet != Diet.TRANSITORY_THIN_TO_WEQCCFAT
//				&& baseWeqCc.mDiet != Diet.TRANSITORY_WEQCCREFATTEN
				) {
			for (final CongruenceClosure<NODE> lab : getDisjuncts()) {
				for (final NODE el : lab.getAllElements()) {
					if (CongruenceClosure.dependsOnAny(el,
							mWeakEquivalenceGraph.getWeqCcManager().getAllWeqPrimedNodes())) {
						assert false;
						return false;
					}
				}
			}
		}

		// note 6.1.2018: commented this out when removing projectToElements from meet operation on weq labels
		//  project can be done by operations using the meet afterwards...
//		if (baseWeqCc != null && baseWeqCc.mDiet == Diet.THIN) {
//			// in THIN-mode: check that labels are free of constraints that don't contain weq nodes
//			for (final DISJUNCT lab : getDisjuncts()) {
//				assert ((CongruenceClosure<NODE>) lab).assertHasOnlyWeqVarConstraints(mWeakEquivalenceGraph.getWeqCcManager().getAllWeqNodes());
//			}
//		}

		return sanityCheckDontEnforceProjectToWeqVars(mWeakEquivalenceGraph.mWeqCc);
	}


	/**
	 * Note: happens in place currently, i.e. no new label and weqGraph are created.. (different from meetWithWeqGpa..)
	 */
	void meetWithCcGpa() {
		final Set<CongruenceClosure<NODE>> newLabelContents = new HashSet<>();

		for (final CongruenceClosure<NODE> disjunct : getDisjuncts()) {
			assert disjunct instanceof CongruenceClosure<?>;

			if (disjunct.isTautological()) {
				// we have one "true" disjunct --> the whole disjunction is tautological
				if (getNumberOfDisjuncts() == 1) {
					return;
				}
				setToTrue(mWeqCcManager.getCcManager().unfreeze(mWeakEquivalenceGraph.mEmptyDisjunct));
				return;
			}

			final CongruenceClosure<NODE> ccfatDisjunct = mWeqCcManager.getCcManager().unfreezeIfNecessary(disjunct);

			mWeqCcManager.meet(ccfatDisjunct,
						mWeakEquivalenceGraph.mWeqCc.getCongruenceClosure(),
						mWeakEquivalenceGraph.mWeqCc.getElementCurrentlyBeingRemoved(),
						true);

			if (ccfatDisjunct.isInconsistent()) {
				/* label element is inconsistent with the current gpa
				 * --> omit it from the new label
				 */
				continue;
			}
			if (ccfatDisjunct.isTautological()) {
				assert false : "this should never happen because if the meet is tautological then mLabel.get(i)"
						+ "is, too, right?";
				// we have one "true" disjunct --> the whole disjunction is tautological
				setToTrue(mWeqCcManager.getCcManager().unfreeze(mWeakEquivalenceGraph.mEmptyDisjunct));
				return;
			}
			newLabelContents.add(ccfatDisjunct);
		}
		assert newLabelContents.size() <= 1 || !newLabelContents.stream().anyMatch(c -> c.isTautological());

		setNewLabelContents(newLabelContents);

		assert sanityCheckDontEnforceProjectToWeqVars(mWeakEquivalenceGraph.mWeqCc);
	}

	private void setNewLabelContents(final Collection<CongruenceClosure<NODE>> newLabelContents) {
		assert newLabelContents.stream().allMatch(cc -> !mWeakEquivalenceGraph.isFrozen() || cc.isFrozen());
		mDisjuncts.clear();
		mDisjuncts.addAll(newLabelContents);
	}

	/**
	 * Set the contents of this label to a single "true"-disjunct
	 */
	private void setToTrue(final CongruenceClosure<NODE> emptyDisjunct) {
		assert mWeakEquivalenceGraph.isFrozen() == emptyDisjunct.isFrozen();
		mDisjuncts.clear();
		mDisjuncts.add(emptyDisjunct);
	}

	boolean sanityCheckDontEnforceProjectToWeqVars(final WeqCongruenceClosure<NODE> baseWeqCc) {
		if (baseWeqCc != null) {
			for (final CongruenceClosure<NODE> lab : getDisjuncts()) {
				if (!lab.sanityCheckOnlyCc(baseWeqCc.getElementCurrentlyBeingRemoved())) {
					assert false;
					return false;
				}
			}
		}

		// check label normalization
		if (getDisjuncts().stream().anyMatch(pa -> pa.isTautological()) && getNumberOfDisjuncts() != 1) {
			assert false : "missing normalization: if there is one 'true' disjunct, we can drop"
					+ "all other disjuncts";
		return false;
		}

		if (getDisjuncts().stream().anyMatch(pa -> pa.isInconsistent())) {
			assert false : "missing normalization: contains 'false' disjuncts";
			return false;
		}

//		if (!assertWeqVarSelectsHaveCorrectVarForDimension()) {
//			assert false;
//			return false;
//		}

		return true;
	}

	/**
	 * every weq-var q has an associated dimension. At an weq edge a --Phi(q)--b that dimension may never exceed the
	 * dimensionality of a and b.
	 *
	 * @param edgeNodeDimension
	 * @return
	 */
	boolean assertWeqVarSelectsHaveCorrectVarForDimension(final int edgeNodeDimension) {
		for (final CongruenceClosure<NODE> lab : getDisjuncts()) {
			for (final NODE el : lab.getAllElements()) {
				if (!mWeqCcManager.getAllWeqNodes().contains(el)) {
					continue;
				}


				if (mWeqCcManager.getDimensionOfWeqVar(el) >= edgeNodeDimension) {
					assert false;
					return false;
				}
			}
		}
		return true;
	}

	boolean assertElementIsFullyRemoved(final NODE elem) {
		for (final CongruenceClosure<NODE> lab : getDisjuncts()) {
			if (!lab.assertSingleElementIsFullyRemoved(elem)) {
				assert false;
				return false;
			}
		}
		return true;
	}

	WeakEquivalenceGraph<NODE> getWeqGraph() {
		return mWeakEquivalenceGraph;
	}

	public boolean assertDisjunctsAreUnfrozen() {
		for (final CongruenceClosure<NODE> disjunct : getDisjuncts()) {
			if (disjunct.isFrozen()) {
				assert false;
				return false;
			}
		}
		return true;
	}

	public boolean assertDisjunctsAreFrozen() {
		for (final CongruenceClosure<NODE> disjunct : getDisjuncts()) {
			if (!disjunct.isFrozen()) {
				assert false;
				return false;
			}
		}
		return true;
	}

	public void freeze() {
		for (final CongruenceClosure<NODE> disjunct : getDisjuncts()) {
			mWeqCcManager.freezeIfNecessary(disjunct);
		}
		mIsFrozen = true;
	}

	public boolean assertIsSlim() {
		assert assertHasOnlyWeqVarConstraints(mWeqCcManager.getAllWeqNodes());
		assert mWeakEquivalenceGraph.mEmptyDisjunct instanceof CongruenceClosure<?>;

		// probably redundant
		assert DataStructureUtils.intersection(getAppearingNodes(), mWeqCcManager.getAllWeqPrimedNodes()).isEmpty();

		return true;
	}

	public WeakEquivalenceEdgeLabel<NODE> thin(
			final WeakEquivalenceGraph<NODE> newWeqGraph) {
		final Set<CongruenceClosure<NODE>> newLabelContents = new HashSet<>();

		for (final CongruenceClosure<NODE> d : getDisjuncts()) {
			// drop inner WeqGraph if present
//			final CongruenceClosure<NODE> cc = mWeqCcManager.copyCcOnly(d, true);
			final CongruenceClosure<NODE> cc = mWeqCcManager.copyCc(d, true);

			/*
			 * unprime if necessary
			 *  background:
			 *   If the current weqCc is CcFat, we must not do this renaming, because it may be the case that it is
			 *   a weqFat label where we are currently removing something, thus making its labels ccFat..
			 *
			 * putting it differently: scenario: a label in a weq-fat weqcc is a weqcc, i.e. has a weq graph, now if
			 *  we cc-fatten the labels of that weq graph they get the primed weq vars from the weq-fat label, so
			 *  those labels have primed and unprimed weq vars.
			 *
			 *   --> all this is a consequence of the hacky "primed weq vars" business..
			 */
			final CongruenceClosure<NODE> unprimedIfWeqFat;
//			if (mWeakEquivalenceGraph.mWeqCc.mDiet == Diet.WEQCCFAT) {
//				unprimedIfWeqFat = mWeqCcManager.renameVariablesCc(cc,
//						mWeqCcManager.getWeqPrimedVarsToWeqVars(), true);
//			} else {
				unprimedIfWeqFat = cc;
//			}

			// drop constraints that do not constrain a weq variable
			final CongruenceClosure<NODE> thinned =
					mWeqCcManager.projectToElements(unprimedIfWeqFat, mWeqCcManager.getAllWeqNodes(), null, true);

			if (thinned.isTautological()) {
				return new WeakEquivalenceEdgeLabel<>(newWeqGraph, mWeqCcManager.getEmptyCc(true));
			}
			if (thinned.isInconsistent()) {
				// drop inconsistent disjunct
				continue;
			}
			newLabelContents.add(thinned);
		}

		return new WeakEquivalenceEdgeLabel<>(newWeqGraph, newLabelContents);
	}

	public void freezeIfNecessary() {
		if (mIsFrozen) {
			return;
		}
		for (final CongruenceClosure<NODE> disjunct : getDisjuncts()) {
			mWeqCcManager.freezeIfNecessary(disjunct);
		}
		mIsFrozen = true;
	}

	public boolean isFrozen() {
		return mIsFrozen;
	}


	/**
	 * Obtains a set constraint that the given element is constrained to by all disjuncts.
	 *
	 *
	 * @param elem
	 * @return a set of elements that the given elem is guaranteed to be contained in by all disjuncts; null means
	 *   unconstrained
	 */
	public Set<SetConstraint<NODE>> getContainsConstraintForElement(final NODE elem) {
		Set<SetConstraint<NODE>> resultConstraint = null;

		// joining through union..
		for (final CongruenceClosure<NODE> d : mDisjuncts) {
			final Set<SetConstraint<NODE>> cc = d.getContainsConstraintForElement(elem);
			if (cc == null) {
				// unconstrained in one disjunct --> unconstrained overall
				return null;
			}

			if (resultConstraint == null) {
				resultConstraint = cc;
			} else {
				resultConstraint = mWeqCcManager.getCcManager().getSetConstraintManager().join(
						mWeakEquivalenceGraph.mWeqCc.getCongruenceClosure().getLiteralSetConstraints(),
						resultConstraint, cc);
			}
		}

		return resultConstraint;
	}

}
