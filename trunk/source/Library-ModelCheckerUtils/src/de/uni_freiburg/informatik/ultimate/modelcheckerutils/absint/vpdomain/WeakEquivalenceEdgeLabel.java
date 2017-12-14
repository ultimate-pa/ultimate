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
package de.uni_freiburg.informatik.ultimate.modelcheckerutils.absint.vpdomain;

import java.util.ArrayList;
import java.util.Collection;
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
import de.uni_freiburg.informatik.ultimate.util.datastructures.congruenceclosure.CongruenceClosure;
import de.uni_freiburg.informatik.ultimate.util.datastructures.congruenceclosure.ICongruenceClosure;
import de.uni_freiburg.informatik.ultimate.util.datastructures.congruenceclosure.RemoveCcElement;
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

	private static final boolean MEET_IN_PLACE = true;

	private static final boolean MEET_WITH_GPA_ON_REPORTCHANGE = false;

	private final WeakEquivalenceGraph<NODE> mWeakEquivalenceGraph;

	private final WeqCcManager<NODE> mWeqCcManager;

	private final Set<CongruenceClosure<NODE>> mDisjuncts;


	/**
	 * Copy constructor.
	 *
	 * @param original
	 * @param weakEquivalenceGraph TODO
	 */
	WeakEquivalenceEdgeLabel(final WeakEquivalenceGraph<NODE> weakEquivalenceGraph,
			final WeakEquivalenceEdgeLabel<NODE> original) {
		mWeakEquivalenceGraph = weakEquivalenceGraph;
		mWeqCcManager = weakEquivalenceGraph.getWeqCcManager();
		mDisjuncts = new HashSet<>(original.getNumberOfDisjuncts());
		for (final CongruenceClosure<NODE> l : original.getDisjuncts()) {
			assert !l.isInconsistent();
			assert !l.isTautological() || original.getDisjuncts().size() == 1;
			assert l.isFrozen();
			mDisjuncts.add(mWeqCcManager.copyCcNoRemInfoUnfrozen(l));
		}
		assert sanityCheck();
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
		assert newLabelContents.stream().allMatch(cc -> cc.isFrozen());
		mWeakEquivalenceGraph = weakEquivalenceGraph;
		mWeqCcManager = weakEquivalenceGraph.getWeqCcManager();
		mDisjuncts = mWeqCcManager.filterRedundantCcs(newLabelContents);
		if (mDisjuncts.size() == 1 && mDisjuncts.iterator().next().isInconsistent()) {
			//case mLabel = "[False]" -- filterRedundantCcs leaves this case so we have to clean up manually to "[]"
			mDisjuncts.clear();
		}
		assert sanityCheck();
	}

	/**
	 * Constructs an empty edge. (labeled "true")
	 * @param weakEquivalenceGraph TODO
	 */
	WeakEquivalenceEdgeLabel(final WeakEquivalenceGraph<NODE> weakEquivalenceGraph) {
		mWeakEquivalenceGraph = weakEquivalenceGraph;
		mWeqCcManager = weakEquivalenceGraph.getWeqCcManager();
		mDisjuncts = new HashSet<>();
		mDisjuncts.add(mWeqCcManager.getEmptyCc(MEET_IN_PLACE));
		assert sanityCheck();
	}

	/**
	 *
	 * @return a copy of this weq edge where all disjuncts have been joined into one
	 */
	WeakEquivalenceEdgeLabel<NODE> flatten(final WeakEquivalenceGraph<NODE> weqGraphForFlattenedLabel) {
		if (isInconsistent()) {
			return this;
		}
		return new WeakEquivalenceEdgeLabel<NODE>(weqGraphForFlattenedLabel, Collections.singleton(
				getDisjuncts().stream().reduce((cc1, cc2) -> mWeqCcManager.join(cc1, cc2)).get()));
	}

	void setExternalRemInfo(final RemoveCcElement<NODE> remInfo) {
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
			RemoveCcElement.removeSimpleElementDontIntroduceNewNodes(lab, firstDimWeqVarNode);
		}
		assert sanityCheckDontEnforceProjectToWeqVars(mWeakEquivalenceGraph.mPartialArrangement);
	}

	/**
	 *
	 * @param elem
	 * @param useWeqGpaMode
	 * @return a set containing all nodes that have been added to the label's Ccs during execution of this method
	 */
	Set<NODE> projectSimpleElement(final NODE elem, final boolean useWeqGpaMode) {
		if (isTautological()) {
			return Collections.emptySet();
		}
		if (isInconsistent()) {
			return Collections.emptySet();
		}

		final Set<NODE> nodesToAddToGpa = new HashSet<>();

		final List<CongruenceClosure<NODE>> newLabelContents = new ArrayList<>(getNumberOfDisjuncts());
		for (final CongruenceClosure<NODE> lab : getDisjuncts()) {
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
				RemoveCcElement.removeSimpleElementDontIntroduceNewNodes(lab, elem);
			}

			assert lab.assertSingleElementIsFullyRemoved(elem);

			if (lab.isTautological()) {
				// a disjunct became "true" through projection --> the whole disjunction is tautological
				setToTrue();
				return Collections.emptySet();
			}
			assert lab.sanityCheckOnlyCc(mWeakEquivalenceGraph.mPartialArrangement.getElementCurrentlyBeingRemoved());

			final CongruenceClosure<NODE> lab2;
			if (useWeqGpaMode) {
				// unprime weqvars
				lab2 = mWeqCcManager.copyCcNoRemInfo(lab);
				lab2.transformElementsAndFunctions(
						node -> node.renameVariables(mWeakEquivalenceGraph.getWeqCcManager().getWeqPrimedVarsToWeqVars()));
			} else {
				lab2 = lab;
			}

			final CongruenceClosure<NODE> newLab = mWeqCcManager.projectToElements(lab2,
					mWeakEquivalenceGraph.getWeqCcManager().getAllWeqNodes(),
					mWeakEquivalenceGraph.mPartialArrangement.getElementCurrentlyBeingRemoved());
			assert newLab.assertSingleElementIsFullyRemoved(elem);
			assert !newLab.isTautological();
			assert newLab.sanityCheckOnlyCc(mWeakEquivalenceGraph.mPartialArrangement.getElementCurrentlyBeingRemoved());
			newLabelContents.add(newLab);
		}
		setNewLabelContents(newLabelContents);
		assert getDisjuncts().stream().allMatch(l -> l.assertSingleElementIsFullyRemoved(elem));
		assert sanityCheck();
		return nodesToAddToGpa;
	}

	private int getNumberOfDisjuncts() {
		return mDisjuncts.size();
	}

	WeakEquivalenceEdgeLabel<NODE> projectToElements(final Set<NODE> allWeqNodes) {
		if (isInconsistent()) {
			return this;
		}
		final Set<CongruenceClosure<NODE>> newLabelContents = new HashSet<>();
		for (final CongruenceClosure<NODE> item : getDisjuncts()) {
			//			newLabelContents.add(item.projectToElements(allWeqNodes,
//					mWeakEquivalenceGraph.mPartialArrangement.getElementCurrentlyBeingRemoved()));
			final CongruenceClosure<NODE> projected = mWeqCcManager.projectToElements(item, allWeqNodes,
					mWeakEquivalenceGraph.mPartialArrangement.getElementCurrentlyBeingRemoved());
			newLabelContents.add(projected);
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
	void inOrDecreaseWeqVarIndices(final int inOrDecrease, final List<NODE> weqVarsForThisEdge) {
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
										mWeqCcManager.getWeqVariableForDimension(newDim, nodeI.getSort()));
							}
						}
						this.transformElements(e -> e.renameVariables(substitutionMapping));
						assert sanityCheckDontEnforceProjectToWeqVars(mWeakEquivalenceGraph.mPartialArrangement);
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
	WeakEquivalenceEdgeLabel<NODE> reportChangeInGroundPartialArrangement(
			final Predicate<CongruenceClosure<NODE>> reportX) {
		assert this.sanityCheck();

		final Set<CongruenceClosure<NODE>> newLabel = new HashSet<>();

		for (final CongruenceClosure<NODE> disjunct : getDisjuncts()) {
			assert mWeakEquivalenceGraph.mPartialArrangement.sanityCheck();
			assert disjunct.sanityCheckOnlyCc();

			final CongruenceClosure<NODE> meetWgpa;
			if (MEET_WITH_GPA_ON_REPORTCHANGE) {
				meetWgpa = mWeqCcManager.meet(disjunct,
					mWeakEquivalenceGraph.mPartialArrangement.getCongruenceClosure(),
					mWeakEquivalenceGraph.mPartialArrangement.getElementCurrentlyBeingRemoved(),
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

			if (MEET_WITH_GPA_ON_REPORTCHANGE) {
				// add the strengthened version as the new label element
				final CongruenceClosure<NODE> projected = mWeqCcManager.projectToElements(meetWgpa,
						mWeakEquivalenceGraph.getWeqCcManager().getAllWeqNodes(),
						mWeakEquivalenceGraph.mPartialArrangement.getElementCurrentlyBeingRemoved());
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
		for (final CongruenceClosure<NODE> cc : getDisjuncts()) {
			final List<Term> cube = CongruenceClosureSmtUtils.congruenceClosureToCube(script, cc);
			final Term cubeTerm = SmtUtils.and(script, cube);
			result.add(cubeTerm);
		}
		return result;
	}

	void transformElements(final Function<NODE, NODE> transformer) {
		assert sanityCheckDontEnforceProjectToWeqVars(mWeakEquivalenceGraph.mPartialArrangement);

		for (final CongruenceClosure<NODE> l : getDisjuncts()) {
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
	Set<NODE> getAppearingNodes() {
		final Set<NODE> res = new HashSet<>();
		getDisjuncts().forEach(pa -> res.addAll(pa.getAllElements()));
		return res;
	}

	WeakEquivalenceEdgeLabel<NODE> meet(final WeakEquivalenceEdgeLabel<NODE> otherLabel, final boolean inplace) {
		return meet(otherLabel.getDisjuncts(), inplace);
	}

	WeakEquivalenceEdgeLabel<NODE> meet(final Set<CongruenceClosure<NODE>> paList) {
		return null;
	}

	WeakEquivalenceEdgeLabel<NODE> meet(final Set<CongruenceClosure<NODE>> paList, final boolean inplace) {
		assert sanityCheckDontEnforceProjectToWeqVars(mWeakEquivalenceGraph.mPartialArrangement);

		final Set<CongruenceClosure<NODE>> newLabelContent = new HashSet<>();
		for (final CongruenceClosure<NODE> lc1 : getDisjuncts()) {
			for (final CongruenceClosure<NODE> lc2 : paList) {
				if (inplace) {
					mWeqCcManager.meet(lc1, lc2, false);
				} else {
					final CongruenceClosure<NODE> meet = mWeqCcManager.meet(lc1, lc2, false);
					newLabelContent.add(meet);
				}
			}
		}

		final Set<CongruenceClosure<NODE>> newLabel = mWeqCcManager.filterRedundantCcs(newLabelContent);
		assert newLabel.stream().allMatch(l -> l.sanityCheckOnlyCc());

		final Set<CongruenceClosure<NODE>> newLabelProjected = newLabel.stream()
				.map(l -> mWeqCcManager.projectToElements(l, mWeakEquivalenceGraph.getWeqCcManager().getAllWeqNodes(),
						mWeakEquivalenceGraph.mPartialArrangement.getElementCurrentlyBeingRemoved()))
				.collect(Collectors.toSet());
		assert newLabelProjected.stream().allMatch(l -> l.sanityCheckOnlyCc(
				mWeakEquivalenceGraph.mPartialArrangement.getElementCurrentlyBeingRemoved()));

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
	boolean isStrongerThan(final WeakEquivalenceEdgeLabel<NODE> other) {
		return isStrongerThan(other, CongruenceClosure::isStrongerThan);
	}

	boolean isStrongerThan(final WeakEquivalenceEdgeLabel<NODE> other,
			final BiPredicate<CongruenceClosure<NODE>, CongruenceClosure<NODE>> lowerOrEqual) {
		for (final CongruenceClosure<NODE> paThis : getDisjuncts()) {
			boolean existsWeaker = false;
			for (final CongruenceClosure<NODE> paOther : other.getDisjuncts()) {
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
	WeakEquivalenceEdgeLabel<NODE> union(final WeakEquivalenceEdgeLabel<NODE> other) {
		return this.union(other, null);
	}

	WeakEquivalenceEdgeLabel<NODE> union(final WeakEquivalenceEdgeLabel<NODE> other,
			final PartialOrderCache<CongruenceClosure<NODE>> ccPoCache) {
		assert this.sanityCheck() && other.sanityCheck();
		//			assert this.mLabel.size() < 10 && other.mLabel.size() < 10;
		final List<CongruenceClosure<NODE>> unionList = new ArrayList<>(getNumberOfDisjuncts()
				+ other.getNumberOfDisjuncts());
		unionList.addAll(getDisjuncts());
		unionList.addAll(other.getDisjuncts());

		final Set<CongruenceClosure<NODE>> filtered = ccPoCache == null
				? mWeqCcManager.filterRedundantCcs(new HashSet<>(unionList))
				: mWeqCcManager.filterRedundantCcs(new HashSet<>(unionList), ccPoCache);

				final WeakEquivalenceEdgeLabel<NODE> result = new WeakEquivalenceEdgeLabel<>(mWeakEquivalenceGraph,
						filtered);
				assert result.sanityCheck();
				return result;
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
		if (getNumberOfDisjuncts() < WeqSettings.MAX_NO_EDGELABELDISJUNCTS_FOR_VERBOSE_TO_STRING) {
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
		return sanityCheck(mWeakEquivalenceGraph.mPartialArrangement);
	}

	private boolean sanityCheck(final WeqCongruenceClosure<NODE> groundPartialArrangement) {
		if (mWeakEquivalenceGraph.getWeqCcManager() == null) {
			return true;
		}
		if (mWeakEquivalenceGraph.isEmpty()) {
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
		if (!groundPartialArrangement.mMeetWithGpaCase) {
			for (final CongruenceClosure<NODE> lab : getDisjuncts()) {
				for (final NODE el : lab.getAllElements()) {
					if (CongruenceClosure.dependsOnAny(el, mWeakEquivalenceGraph.getWeqCcManager().getAllWeqPrimedNodes())) {
						assert false;
						return false;
					}
				}
			}
		}

		// check that labels are free of constraints that don't contain weq nodes
		for (final CongruenceClosure<NODE> lab : getDisjuncts()) {
			assert lab.assertHasOnlyWeqVarConstraints(mWeakEquivalenceGraph.getWeqCcManager().getAllWeqNodes());
		}

		return sanityCheckDontEnforceProjectToWeqVars(mWeakEquivalenceGraph.mPartialArrangement);
	}

	void meetWithWeqGpa(final WeqCongruenceClosure<NODE> originalPa) {

		final List<CongruenceClosure<NODE>> newLabelContents = new ArrayList<>();
		for (final CongruenceClosure<NODE> l : getDisjuncts()) {

			// make a copy of the full abstract state (ground partial arrangement and weak equivalence graph, weqCc)
			//				final WeqCongruenceClosure<NODE> paCopy = new WeqCongruenceClosure<>(originalPa, true);
			WeqCongruenceClosure<NODE> paCopy = mWeqCcManager.makeCopyForWeqMeet(originalPa);


			// make a copy of the label, prime the weq vars
			final CongruenceClosure<NODE> lCopy = mWeqCcManager.copyCcNoRemInfo(l);
			final CongruenceClosure<NODE> labelWithWeqVarsPrimed = mWeqCcManager.renameVariablesCc(lCopy,
					mWeqCcManager.getWeqVarsToWeqPrimedVars());

			// report all constraints from the label into the copy of the weqCc
			for (final Entry<NODE, NODE> eq : labelWithWeqVarsPrimed.getSupportingElementEqualities().entrySet()) {
				if (paCopy.isInconsistent()) {
					break;
				}
				paCopy = mWeqCcManager.reportEquality(paCopy, eq.getKey(), eq.getValue(), MEET_IN_PLACE);
			}
			for (final Entry<NODE, NODE> deq : labelWithWeqVarsPrimed.getElementDisequalities().entrySet()) {
				if (paCopy.isInconsistent()) {
					break;
				}
				paCopy = mWeqCcManager.reportDisequality(paCopy, deq.getKey(), deq.getValue());
			}

			if (paCopy.isTautological()) {
				setToTrue();
				return;
			}

			if (!paCopy.isInconsistent()) {
				newLabelContents.add(paCopy.getCongruenceClosure());
			}
		}

		setNewLabelContents(newLabelContents);

		assert sanityCheckDontEnforceProjectToWeqVars(mWeakEquivalenceGraph.mPartialArrangement);

	}

	void meetWithCcGpa() {
		final Set<CongruenceClosure<NODE>> newLabelContents = new HashSet<>();

		for (final CongruenceClosure<NODE> disjunct : getDisjuncts()) {
			if (disjunct.isTautological()) {
				// we have one "true" disjunct --> the whole disjunction is tautological
				if (getNumberOfDisjuncts() == 1) {
					return;
				}
				setToTrue();
				return;
			}
			final CongruenceClosure<NODE> meet = mWeqCcManager.meet(disjunct,
						mWeakEquivalenceGraph.mPartialArrangement.getCongruenceClosure(),
						mWeakEquivalenceGraph.mPartialArrangement.getElementCurrentlyBeingRemoved(),
						false);

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
				setToTrue();
				return;
			}
			newLabelContents.add(meet);
		}
		assert newLabelContents.size() <= 1 || !newLabelContents.stream().anyMatch(c -> c.isTautological());

		setNewLabelContents(newLabelContents);

		assert sanityCheckDontEnforceProjectToWeqVars(mWeakEquivalenceGraph.mPartialArrangement);
	}

	private void setNewLabelContents(final Collection<CongruenceClosure<NODE>> newLabelContents) {
		assert newLabelContents.stream().allMatch(cc -> cc.isFrozen());
		mDisjuncts.clear();
		mDisjuncts.addAll(newLabelContents);
	}

	/**
	 * Set the contents of this label to a single "true"-disjunct
	 */
	private void setToTrue() {
		mDisjuncts.clear();
		mDisjuncts.add(mWeqCcManager.getEmptyCc(MEET_IN_PLACE));
	}

	boolean sanityCheckDontEnforceProjectToWeqVars(final ICongruenceClosure<NODE> groundPartialArrangement) {
		for (final CongruenceClosure<NODE> lab : getDisjuncts()) {
			if (!lab.sanityCheckOnlyCc(groundPartialArrangement.getElementCurrentlyBeingRemoved())) {
				assert false;
				return false;
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

	public void freeze() {
		for (final CongruenceClosure<NODE> disjunct : getDisjuncts()) {
			disjunct.freeze();
		}
	}
}
