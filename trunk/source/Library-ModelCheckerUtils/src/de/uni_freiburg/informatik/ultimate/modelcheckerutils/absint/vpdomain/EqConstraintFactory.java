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
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.ModelCheckerUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.util.datastructures.CrossProducts;
import de.uni_freiburg.informatik.ultimate.util.datastructures.congruenceclosure.CongruenceClosureComparator;

/**
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 * @param <NODE>
 */
public class EqConstraintFactory<NODE extends IEqNodeIdentifier<NODE>> {

//	/**
//	 * more of a dummy right now, for keeping the old in-place/mutable data code
//	 */
//	private static final boolean INPLACE = false;

	private final EqConstraint<NODE> mBottomConstraint;

	private final EqConstraint<NODE> mEmptyConstraint;

	private final EqDisjunctiveConstraint<NODE> mEmptyDisjunctiveConstraint;

	private final AbstractNodeAndFunctionFactory<NODE, Term> mEqNodeAndFunctionFactory;

	private final IUltimateServiceProvider mServices;

	private int mConstraintIdCounter;

	private final WeqCcManager<NODE> mWeqCcManager;

	private final ManagedScript mMgdScript;

	private final boolean mIsDebugMode;

	private final ILogger mLogger;

	public EqConstraintFactory(final AbstractNodeAndFunctionFactory<NODE, Term> eqNodeAndFunctionFactory,
			final IUltimateServiceProvider services, final ManagedScript mgdScript) {
		mLogger = services.getLoggingService().getLogger(ModelCheckerUtils.PLUGIN_ID);

		mMgdScript = mgdScript;

		mWeqCcManager = new WeqCcManager<>(mLogger, new WeqCongruenceClosureComparator<NODE>(),
				new CongruenceClosureComparator<NODE>(), mMgdScript, eqNodeAndFunctionFactory);

		mBottomConstraint = new EqBottomConstraint<>(this);
		mBottomConstraint.freeze();

		mEmptyConstraint = new EqConstraint<>(1, mWeqCcManager.getEmptyWeqCc(true), this);
		mEmptyConstraint.freeze();
		mEmptyDisjunctiveConstraint = new EqDisjunctiveConstraint<>(Collections.singleton(mEmptyConstraint), this);

		mConstraintIdCounter = 2;

		mServices = services;

		mIsDebugMode = true;

		mEqNodeAndFunctionFactory = eqNodeAndFunctionFactory;

	}

	/**
	 *
	 * @param modifiable
	 * @return
	 */
	public EqConstraint<NODE> getEmptyConstraint(final boolean modifiable) {
		if (modifiable) {
			return new EqConstraint<>(mConstraintIdCounter++, mWeqCcManager.getEmptyWeqCc(true), this);
		} else {
			return mEmptyConstraint;
		}
	}

	public EqConstraint<NODE> getBottomConstraint() {
		return mBottomConstraint;
	}

	/**
	 * Makes a copy of the given constraint that is not frozen.
	 *
	 * @param constraint
	 * @return
	 */
	public EqConstraint<NODE> unfreeze(final EqConstraint<NODE> constraint) {
		assert constraint.isFrozen();
		if (constraint.isBottom()) {
			return constraint;
		}
//		final WeqCongruenceClosure<NODE> weqCcCopy = mWeqCcManager.getFrozenCopy(constraint.getWeqCc());
		final WeqCongruenceClosure<NODE> weqCcCopy = mWeqCcManager.copyWeqCc(constraint.getWeqCc(), false);
		return new EqConstraint<>(mConstraintIdCounter++, weqCcCopy, this);
	}

	/**
	 * Return a constraint built from the given weqcc, result is frozen.
	 *
	 * @param newWeqCc
	 * @return
	 */
	public EqConstraint<NODE> getEqConstraint(final WeqCongruenceClosure<NODE> newWeqCc, final boolean modifiable) {
		if (newWeqCc.isInconsistent()) {
			return getBottomConstraint();
		}
		assert modifiable != newWeqCc.isFrozen();
		final EqConstraint<NODE> result = new EqConstraint<>(mConstraintIdCounter++, newWeqCc, this);
		if (!modifiable) {
			result.superficialFreeze();
		}
		return result;
	}

	public EqDisjunctiveConstraint<NODE>
			getDisjunctiveConstraint(final Collection<EqConstraint<NODE>> constraintList) {
		assert !constraintList.stream().filter(cons -> cons == null).findAny().isPresent();
		// TODO: do we want full-fledged filtering for weakest constraints here? (e.g. via PartialOrderCache, like in
		//    CcManager)

		// if one of the disjuncts is "top", remove all other disjuncts
		if (constraintList.stream().filter(cons -> cons.isTop()).findAny().isPresent()) {
			return getTopDisjunctiveConstraint();
		}

		// filter out bottom-constraints among the disjuncts
		final Collection<EqConstraint<NODE>> bottomsFiltered = constraintList.stream()
				.filter(cons -> !(cons instanceof EqBottomConstraint)).collect(Collectors.toSet());

		return new EqDisjunctiveConstraint<NODE>(bottomsFiltered, this);
	}

	public EqConstraint<NODE> conjoin(final EqConstraint<NODE> constraint1, final EqConstraint<NODE> constraint2,
			final boolean inplace) {
		if (constraint1.isBottom()) {
			return constraint1;
		}
		if (constraint2.isBottom() && !inplace) {
			return constraint2;
		}
		if (constraint1.isTop() && !inplace) {
			return constraint2;
		}
		if (constraint2.isTop()) {
			return constraint1;
		}

		if (!inplace) {
			freezeIfNecessary(constraint1);
		}

		assert inplace != constraint1.isFrozen();

		final WeqCongruenceClosure<NODE> newPa = mWeqCcManager.meet(constraint1.getWeqCc(), constraint2.getWeqCc(),
				inplace);

		assert inplace != newPa.isFrozen();

		if (inplace) {
			return constraint1;
		} else {
			final EqConstraint<NODE> res = getEqConstraint(newPa, false);
			return res;
		}
	}

	private void freezeIfNecessary(final EqConstraint<NODE> constraint1) {
		if (!constraint1.isFrozen()) {
			constraint1.freeze();
		}
	}

	/**
	 * conjunction/intersection/join
	 *
	 * @param conjuncts
	 * @return
	 */
	public EqDisjunctiveConstraint<NODE> conjoinDisjunctiveConstraints(
			final List<EqDisjunctiveConstraint<NODE>> conjuncts) {
		final List<Set<EqConstraint<NODE>>> listOfConstraintSets = conjuncts.stream()
				.map(conjunct -> conjunct.getConstraints()).collect(Collectors.toList());

		final List<List<EqConstraint<NODE>>> crossProduct =
				CrossProducts.crossProductOfSets(listOfConstraintSets);

		// for each tuple in the cross product: construct the meet, and add it to the resulting constraintList
		final List<EqConstraint<NODE>> constraintList = crossProduct.stream()
			.map(tuple -> tuple.stream()
					.reduce((constraint1, constraint2) -> conjoin(constraint1, constraint2, false)).get())
			.collect(Collectors.toList());
		return getDisjunctiveConstraint(constraintList);
	}

	public EqConstraint<NODE> addWeakEquivalence(final NODE array1, final NODE array2, final NODE storeIndex,
			final EqConstraint<NODE> inputConstraint, final boolean inplace) {
		assert VPDomainHelpers.haveSameType(array1, array2);
		if (inplace) {
			assert !inputConstraint.isFrozen();
			mWeqCcManager.reportWeakEquivalence(inputConstraint.getWeqCc(), array1, array2, storeIndex, true);
			return inputConstraint;

//			final EqConstraint<NODE> newConstraint = unfreeze(inputConstraint);
//			newConstraint.reportWeakEquivalenceInPlace(array1, array2, storeIndex);
//			if (newConstraint.isInconsistent()) {
//				return mBottomConstraint;
//			}
//			newConstraint.freeze();
//			return newConstraint;
		} else {
			final WeqCongruenceClosure<NODE> newWeqCc = mWeqCcManager.reportWeakEquivalence(inputConstraint.getWeqCc(),
					array1, array2, storeIndex, false);
			return getEqConstraint(newWeqCc, false);
		}
	}

	public EqDisjunctiveConstraint<NODE> disjoinDisjunctiveConstraints(
			final EqDisjunctiveConstraint<NODE> disjunct1,
			final EqDisjunctiveConstraint<NODE> disjunct2) {
		final Set<EqConstraint<NODE>> allConjunctiveConstraints = new HashSet<>();
		allConjunctiveConstraints.addAll(disjunct1.getConstraints());
		allConjunctiveConstraints.addAll(disjunct2.getConstraints());
		return getDisjunctiveConstraint(allConjunctiveConstraints);
	}

	/**
	 * disjunction/union/meet
	 *
	 * @param disjuncts
	 * @return
	 */
	public EqDisjunctiveConstraint<NODE> disjoinDisjunctiveConstraints(
			final List<EqDisjunctiveConstraint<NODE>> disjuncts) {

		final Set<EqConstraint<NODE>> allConjunctiveConstraints = new HashSet<>();
		for (final EqDisjunctiveConstraint<NODE> disjunct : disjuncts) {
			allConjunctiveConstraints.addAll(disjunct.getConstraints());
		}

		return getDisjunctiveConstraint(allConjunctiveConstraints);
	}

	/**
	 * Disjoin two (conjunctive) EqConstraints without creating an EqDisjunctiveConstraint -- this operation may loose
	 * information.
	 *
	 * Essentially, we only keep constraints that are present in both input constraints.
	 *
	 * @param constraint
	 * @param constraint2
	 * @return
	 */
	public EqConstraint<NODE> disjoin(final EqConstraint<NODE> constraint1, final EqConstraint<NODE> constraint2) {
		final List<EqConstraint<NODE>> disjuncts = new ArrayList<>();
		disjuncts.add(constraint1);
		disjuncts.add(constraint2);
		return getDisjunctiveConstraint(disjuncts).flatten();
	}

	public EqConstraint<NODE> addEquality(final NODE node1, final NODE node2,
			final EqConstraint<NODE> inputConstraint, final boolean inplace) {
		if (inputConstraint.isBottom()) {
			return inputConstraint;
		}

		if (inputConstraint.areEqual(node1, node2)) {
			// the given identifiers are already equal in the originalState
			return inputConstraint;
		}

		if (inputConstraint.areUnequal(node1, node2) && !inplace) {
			return getBottomConstraint();
		}

		if (inplace) {
			mWeqCcManager.reportEquality(inputConstraint.getWeqCc(), node1, node2, true);
			return inputConstraint;
		} else {
			final WeqCongruenceClosure<NODE> newWeqCc = mWeqCcManager.reportEquality(inputConstraint.getWeqCc(),
					node1, node2, false);
			return getEqConstraint(newWeqCc, false);
		}
	}


	public EqConstraint<NODE> addDisequality(final NODE node1, final NODE node2,
			final EqConstraint<NODE> inputConstraint, final boolean inplace) {
		assert inplace != inputConstraint.isFrozen();
		if (inputConstraint.isBottom()) {
			return inputConstraint;
		}

		if (inputConstraint.areUnequal(node1, node2)) {
			// the given identifiers are already equal in the input constraint -- nothing to do
			return inputConstraint;
		}

		/*
		 * check if the disequality introduces a contradiction, return bottom in that case
		 */
		if (inputConstraint.areEqual(node1, node2) && !inplace) {
			return getBottomConstraint();
		}

		if (inplace) {
			mWeqCcManager.reportDisequality(inputConstraint.getWeqCc(), node1, node2, true);
			return inputConstraint;
		} else {
			final WeqCongruenceClosure<NODE> newWeqCc = mWeqCcManager.reportDisequality(inputConstraint.getWeqCc(),
					node1, node2, false);
			return getEqConstraint(newWeqCc, false);
		}
	}


	public EqDisjunctiveConstraint<NODE> renameVariables(final EqDisjunctiveConstraint<NODE> constraint,
			final Map<Term, Term> substitutionMapping) {
		final Collection<EqConstraint<NODE>> constraintList = new ArrayList<>();

		for (final EqConstraint<NODE> oldConstraint : constraint.getConstraints()) {
			final EqConstraint<NODE> newConstraint = renameVariables(oldConstraint, substitutionMapping, false);
			constraintList.add(newConstraint);
		}

		return getDisjunctiveConstraint(constraintList);
	}

	private EqConstraint<NODE> renameVariables(final EqConstraint<NODE> oldConstraint,
			final Map<Term, Term> substitutionMapping, final boolean inplace) {
		if (inplace) {
			mWeqCcManager.renameVariables(oldConstraint.getWeqCc(), substitutionMapping, true);
			return oldConstraint;
		} else {
			final WeqCongruenceClosure<NODE> newWeqCc = mWeqCcManager.renameVariables(oldConstraint.getWeqCc(),
				substitutionMapping, false);
			return getEqConstraint(newWeqCc, false);
		}
	}

	/**
	 *
	 * @param termsToProjectAway
	 * @return
	 */
	public EqConstraint<NODE> projectExistentially(final Collection<Term> termsToProjectAway,
			final EqConstraint<NODE> original, final boolean inplace) {
		assert original.isFrozen();
		assert original.sanityCheck();
		if (original.isBottom()) {
			return original;
		}

		if (mIsDebugMode) {
			mLogger.debug("project variables " + termsToProjectAway + " from " + original.hashCode());
		}

		final EqConstraint<NODE> result;
		if (inplace) {
			for (final Term term : termsToProjectAway) {
				if (!getEqNodeAndFunctionFactory().hasNode(term)) {
					// nothing to do
					continue;
				}
				if (original.isInconsistent()) {
					postProjectHelper(original, termsToProjectAway, original);
					return original;
				}

				final NODE nodeToHavoc = getEqNodeAndFunctionFactory().getExistingNode(term);
				mWeqCcManager.projectAway(original.getWeqCc(), nodeToHavoc);
			}
			postProjectHelper(original, termsToProjectAway, original);
			return original;
		} else {
			WeqCongruenceClosure<NODE> newWeqCc = original.getWeqCc();
			for (final Term term : termsToProjectAway) {
				if (!getEqNodeAndFunctionFactory().hasNode(term)) {
					continue;
				}
				if (newWeqCc.isInconsistent()) {
					return getBottomConstraint();
				}

				// havoccing an element
				final NODE nodeToProjectAway = getEqNodeAndFunctionFactory().getExistingNode(term);
				newWeqCc = mWeqCcManager.projectAway(newWeqCc, nodeToProjectAway);

				if (newWeqCc.isInconsistent()) {
					return getBottomConstraint();
				}

				assert newWeqCc.sanityCheck();
			}
			result = getEqConstraint(newWeqCc, false);
			postProjectHelper(original, termsToProjectAway, result);
			return result;
		}


	}

	private void postProjectHelper(final EqConstraint<NODE> original, final Collection<Term> termsToProjectAway,
			final EqConstraint<NODE> result) {
		assert VPDomainHelpers.constraintFreeOfVars(termsToProjectAway, result, getMgdScript().getScript()) :
					"resulting constraint still has at least one of the to-be-projected vars";

		if (mIsDebugMode) {
			mLogger.debug("projected variables " + termsToProjectAway + " from " + original.hashCode() + " result: "
					+ result);
		}
	}

	public AbstractNodeAndFunctionFactory<NODE, Term> getEqNodeAndFunctionFactory() {
		return mEqNodeAndFunctionFactory;
	}

	public EqDisjunctiveConstraint<NODE> getTopDisjunctiveConstraint() {
		return mEmptyDisjunctiveConstraint;
	}

	public ManagedScript getMgdScript() {
		return mMgdScript;
	}

	@Override
	public String toString() {
		return this.getClass().getSimpleName();
	}

	public WeqCcManager<NODE> getWeqCcManager() {
		return mWeqCcManager;
	}

	public ILogger getLogger() {
		return mLogger;
	}

	public boolean isDebugMode() {
		return mIsDebugMode;
	}

	/**
	 *
	 * @param modifiable return a modifiable, fresh constraint
	 * @return
	 */
	public EqDisjunctiveConstraint<NODE> getEmptyDisjunctiveConstraint(final boolean modifiable) {
		return getDisjunctiveConstraint(Collections.singleton(getEmptyConstraint(modifiable)));
	}
}
