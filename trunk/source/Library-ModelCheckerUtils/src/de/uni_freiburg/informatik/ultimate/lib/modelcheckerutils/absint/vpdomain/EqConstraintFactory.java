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
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.ModelCheckerUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramConst;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.util.datastructures.CrossProducts;
import de.uni_freiburg.informatik.ultimate.util.datastructures.congruenceclosure.CongruenceClosureComparator;
import de.uni_freiburg.informatik.ultimate.util.statistics.BenchmarkWithCounters;

/**
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 * @param <NODE>
 */
public class EqConstraintFactory<NODE extends IEqNodeIdentifier<NODE>> {

	private final EqConstraint<NODE> mBottomConstraint;

	private final EqConstraint<NODE> mEmptyConstraint;

	private final EqDisjunctiveConstraint<NODE> mEmptyDisjunctiveConstraint;

	private final AbstractNodeAndFunctionFactory<NODE, Term> mEqNodeAndFunctionFactory;

	private final IUltimateServiceProvider mServices;

	private int mConstraintIdCounter;

	private final WeqCcManager<NODE> mWeqCcManager;

	private final ManagedScript mMgdScript;

	/*
	 * rather general flag, when this is off, we try to omit everything that costs time/memory and is not immediately
	 * needed.
	 */
	private final boolean mIsDebugMode;

	private final ILogger mLogger;

	private final BenchmarkWithCounters mBenchmark;

	private final Set<IProgramConst> mNonTheoryLiterals;

	public EqConstraintFactory(final AbstractNodeAndFunctionFactory<NODE, Term> eqNodeAndFunctionFactory,
			final IUltimateServiceProvider services, final ManagedScript mgdScript, final WeqSettings settings,
			final boolean debugMode, final Set<IProgramConst> nonTheoryLiterals) {
		mLogger = services.getLoggingService().getLogger(ModelCheckerUtils.PLUGIN_ID);

		mMgdScript = mgdScript;

		mNonTheoryLiterals = nonTheoryLiterals;

		final Set<NODE> nonTheoryLiteralNodes = nonTheoryLiterals.stream()
				.map(pc -> eqNodeAndFunctionFactory.getOrConstructNode(pc.getTerm())).collect(Collectors.toSet());
		mWeqCcManager = new WeqCcManager<>(mLogger, new WeqCongruenceClosureComparator<NODE>(),
				new CongruenceClosureComparator<NODE>(), mMgdScript, eqNodeAndFunctionFactory, settings, debugMode,
				nonTheoryLiteralNodes);

		mBottomConstraint = new EqBottomConstraint<>(this);
		mBottomConstraint.freezeIfNecessary();

		mEmptyConstraint = new EqConstraint<>(1, mWeqCcManager.getEmptyWeqCc(true), this);
		mEmptyConstraint.freezeIfNecessary();
		mEmptyDisjunctiveConstraint = new EqDisjunctiveConstraint<>(Collections.singleton(mEmptyConstraint), this);

		mConstraintIdCounter = 2;

		mServices = services;

		mIsDebugMode = !true;
		if (mIsDebugMode) {
			mBenchmark = new BenchmarkWithCounters();
			mBenchmark.registerCountersAndWatches(BmNames.getNames());
		} else {
			mBenchmark = null;
		}

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
		}
		return mEmptyConstraint;
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
		debugStart(BmNames.UNFREEZE);
		if (constraint.isBottom()) {
			debugEnd(BmNames.UNFREEZE);
			return constraint;
		}
		final WeqCongruenceClosure<NODE> weqCcCopy = mWeqCcManager.copyWeqCc(constraint.getWeqCc(), false);
		final EqConstraint<NODE> result = new EqConstraint<>(mConstraintIdCounter++, weqCcCopy, this);
		debugEnd(BmNames.UNFREEZE);
		return result;
	}

	private void debugStart(final BmNames name) {
		if (mIsDebugMode) {
			mBenchmark.incrementCounter(name.name());
			mBenchmark.unpauseWatch(name.name());
		}
	}

	private void debugEnd(final BmNames name) {
		if (mIsDebugMode) {
			mBenchmark.pauseWatch(name.name());
		}
	}

	/**
	 * Return a constraint built from the given weqcc, result is frozen.
	 *
	 * @param newWeqCc
	 * @return
	 */
	public EqConstraint<NODE> getEqConstraint(final WeqCongruenceClosure<NODE> newWeqCc, final boolean modifiable) {
		if (newWeqCc.isInconsistent(mWeqCcManager.getSettings().closeAllEqConstraints())) {
			return getBottomConstraint();
		}
		assert modifiable != newWeqCc.isFrozen();
		final EqConstraint<NODE> result = new EqConstraint<>(mConstraintIdCounter++, newWeqCc, this);
		if (!modifiable) {
			result.superficialFreeze();
		}
		return result;
	}

	public EqDisjunctiveConstraint<NODE> getDisjunctiveConstraint(final Collection<EqConstraint<NODE>> constraintList) {
		assert !constraintList.stream().filter(cons -> cons == null).findAny().isPresent();
		// TODO: do we want full-fledged filtering for weakest constraints here? (e.g. via PartialOrderCache, like in
		// CcManager)

		// if one of the disjuncts is "top", remove all other disjuncts
		if (constraintList.stream().filter(cons -> cons.isTop()).findAny().isPresent()) {
			return getEmptyDisjunctiveConstraint(false);
		}

		// filter out bottom-constraints among the disjuncts
		final Collection<EqConstraint<NODE>> bottomsFiltered = constraintList.stream()
				.filter(cons -> !(cons instanceof EqBottomConstraint)).collect(Collectors.toSet());

		return new EqDisjunctiveConstraint<>(bottomsFiltered, this);
	}

	public EqConstraint<NODE> conjoin(final EqConstraint<NODE> constraint1Raw, final EqConstraint<NODE> constraint2,
			final boolean inplace) {
		debugStart(BmNames.CONJOIN);
		if (constraint1Raw.isBottom()) {
			debugEnd(BmNames.CONJOIN);
			return constraint1Raw;
		}
		if (constraint2.isBottom() && !inplace) {
			debugEnd(BmNames.CONJOIN);
			return constraint2;
		}
		if (constraint1Raw.isTop() && !inplace) {
			debugEnd(BmNames.CONJOIN);
			return constraint2;
		}
		if (constraint2.isTop()) {
			debugEnd(BmNames.CONJOIN);
			return constraint1Raw;
		}

		EqConstraint<NODE> constraint1 = constraint1Raw;
		if (!inplace) {
			if (mWeqCcManager.getSettings().closeAllEqConstraints()) {
				constraint1 = closeIfNecessary(constraint1Raw);
			}
			constraint1.freezeIfNecessary();
		}

		// assert !mWeqCcManager.getSettings().closeAllEqConstraints() || constraint2.getWeqCc().isClosed() :
		// "right?..";

		assert inplace != constraint1.isFrozen();

		final WeqCongruenceClosure<NODE> newPa =
				mWeqCcManager.meet(constraint1.getWeqCc(), constraint2.getWeqCc(), inplace);

		assert inplace != newPa.isFrozen();

		if (inplace) {
			debugEnd(BmNames.CONJOIN);
			return constraint1;
		}
		final EqConstraint<NODE> res = getEqConstraint(newPa, false);
		debugEnd(BmNames.CONJOIN);
		return res;
	}

	public EqConstraint<NODE> closeIfNecessary(final EqConstraint<NODE> constraint) {
		if (constraint.isBottom()) {
			return constraint;
		}
		final WeqCongruenceClosure<NODE> weqcc = constraint.getWeqCc();
		if (weqcc.isClosed()) {
			return constraint;
		}
		final WeqCongruenceClosure<NODE> weqccclosed = mWeqCcManager.closeIfNecessary(constraint.getWeqCc());
		return getEqConstraint(weqccclosed, true);
	}

	/**
	 * conjunction/intersection/join
	 *
	 * @param conjuncts
	 * @return
	 */
	public EqDisjunctiveConstraint<NODE>
			conjoinDisjunctiveConstraints(final List<EqDisjunctiveConstraint<NODE>> conjuncts) {
		debugStart(BmNames.CONJOIN_DISJUNCTIVE);
		final List<Set<EqConstraint<NODE>>> listOfConstraintSets =
				conjuncts.stream().map(conjunct -> conjunct.getConstraints()).collect(Collectors.toList());

		final List<List<EqConstraint<NODE>>> crossProduct = CrossProducts.crossProductOfSets(listOfConstraintSets);

		// for each tuple in the cross product: construct the meet, and add it to the resulting constraintList
		final List<EqConstraint<NODE>> constraintList = crossProduct.stream()
				.map(tuple -> tuple.stream()
						.reduce((constraint1, constraint2) -> conjoin(constraint1, constraint2, false)).get())
				.collect(Collectors.toList());
		debugEnd(BmNames.CONJOIN_DISJUNCTIVE);
		return getDisjunctiveConstraint(constraintList);
	}

	public EqConstraint<NODE> addWeakEquivalence(final NODE array1, final NODE array2, final NODE storeIndex,
			final EqConstraint<NODE> inputConstraint, final boolean inplace) {
		assert VPDomainHelpers.haveSameType(array1, array2);
		debugStart(BmNames.ADD_WEAK_EQUALITY);
		if (inplace) {
			assert !inputConstraint.isFrozen();
			mWeqCcManager.reportWeakEquivalence(inputConstraint.getWeqCc(), array1, array2, storeIndex, true);
			debugEnd(BmNames.ADD_WEAK_EQUALITY);
			return inputConstraint;
		}
		final WeqCongruenceClosure<NODE> newWeqCc =
				mWeqCcManager.reportWeakEquivalence(inputConstraint.getWeqCc(), array1, array2, storeIndex, false);
		final EqConstraint<NODE> result = getEqConstraint(newWeqCc, false);
		debugEnd(BmNames.ADD_WEAK_EQUALITY);
		return result;
	}

	public EqDisjunctiveConstraint<NODE> disjoinDisjunctiveConstraints(final EqDisjunctiveConstraint<NODE> disjunct1,
			final EqDisjunctiveConstraint<NODE> disjunct2) {
		debugStart(BmNames.DISJOIN_DISJUNCTIVE);
		final Set<EqConstraint<NODE>> allConjunctiveConstraints = new HashSet<>();
		allConjunctiveConstraints.addAll(disjunct1.getConstraints());
		allConjunctiveConstraints.addAll(disjunct2.getConstraints());
		final EqDisjunctiveConstraint<NODE> result = getDisjunctiveConstraint(allConjunctiveConstraints);
		debugEnd(BmNames.DISJOIN_DISJUNCTIVE);
		return result;
	}

	/**
	 * disjunction/union/meet
	 *
	 * @param disjuncts
	 * @return
	 */
	public EqDisjunctiveConstraint<NODE>
			disjoinDisjunctiveConstraints(final List<EqDisjunctiveConstraint<NODE>> disjuncts) {
		debugStart(BmNames.DISJOIN_DISJUNCTIVE);

		final Set<EqConstraint<NODE>> allConjunctiveConstraints = new HashSet<>();
		for (final EqDisjunctiveConstraint<NODE> disjunct : disjuncts) {
			allConjunctiveConstraints.addAll(disjunct.getConstraints());
		}

		final EqDisjunctiveConstraint<NODE> result = getDisjunctiveConstraint(allConjunctiveConstraints);
		debugEnd(BmNames.DISJOIN_DISJUNCTIVE);
		return result;
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
		debugStart(BmNames.DISJOIN);
		final List<EqConstraint<NODE>> disjuncts = new ArrayList<>();
		disjuncts.add(constraint1);
		disjuncts.add(constraint2);
		final EqConstraint<NODE> result = getDisjunctiveConstraint(disjuncts).flatten();
		debugEnd(BmNames.DISJOIN);
		return result;
	}

	public EqConstraint<NODE> addEquality(final NODE node1, final NODE node2, final EqConstraint<NODE> inputConstraint,
			final boolean inplace) {
		debugStart(BmNames.ADD_EQUALITY);
		if (inputConstraint.isBottom()) {
			debugEnd(BmNames.ADD_EQUALITY);
			return inputConstraint;
		}

		if (inputConstraint.areEqual(node1, node2, false)) {
			// the given identifiers are already equal in the originalState
			debugEnd(BmNames.ADD_EQUALITY);
			return inputConstraint;
		}

		if (inputConstraint.areUnequal(node1, node2, false) && !inplace) {
			debugEnd(BmNames.ADD_EQUALITY);
			return getBottomConstraint();
		}

		if (inplace) {
			mWeqCcManager.reportEquality(inputConstraint.getWeqCc(), node1, node2, true);
			debugEnd(BmNames.ADD_EQUALITY);
			return inputConstraint;
		}
		final WeqCongruenceClosure<NODE> newWeqCc =
				mWeqCcManager.reportEquality(inputConstraint.getWeqCc(), node1, node2, false);
		final EqConstraint<NODE> result = getEqConstraint(newWeqCc, false);
		debugEnd(BmNames.ADD_EQUALITY);
		return result;
	}

	public EqConstraint<NODE> addDisequality(final NODE node1, final NODE node2,
			final EqConstraint<NODE> inputConstraint, final boolean inplace) {
		assert inplace != inputConstraint.isFrozen();
		debugStart(BmNames.ADD_DISEQUALITY);
		if (inputConstraint.isBottom()) {
			debugEnd(BmNames.ADD_DISEQUALITY);
			return inputConstraint;
		}

		if (inputConstraint.areUnequal(node1, node2, false)) {
			// the given identifiers are already equal in the input constraint -- nothing to do
			debugEnd(BmNames.ADD_DISEQUALITY);
			return inputConstraint;
		}

		/*
		 * check if the disequality introduces a contradiction, return bottom in that case
		 */
		if (inputConstraint.areEqual(node1, node2, false) && !inplace) {
			debugEnd(BmNames.ADD_DISEQUALITY);
			return getBottomConstraint();
		}

		if (inplace) {
			mWeqCcManager.reportDisequality(inputConstraint.getWeqCc(), node1, node2, true);
			debugEnd(BmNames.ADD_DISEQUALITY);
			return inputConstraint;
		}
		final WeqCongruenceClosure<NODE> newWeqCc =
				mWeqCcManager.reportDisequality(inputConstraint.getWeqCc(), node1, node2, false);
		final EqConstraint<NODE> result = getEqConstraint(newWeqCc, false);
		debugEnd(BmNames.ADD_DISEQUALITY);
		return result;
	}

	public EqDisjunctiveConstraint<NODE> renameVariables(final EqDisjunctiveConstraint<NODE> constraint,
			final Map<Term, Term> substitutionMapping) {
		debugStart(BmNames.RENAME_VARIABLES_DISJUNCTIVE);
		final Collection<EqConstraint<NODE>> constraintList = new ArrayList<>();

		for (final EqConstraint<NODE> oldConstraint : constraint.getConstraints()) {
			final EqConstraint<NODE> newConstraint = renameVariables(oldConstraint, substitutionMapping, false);
			constraintList.add(newConstraint);
		}

		final EqDisjunctiveConstraint<NODE> result = getDisjunctiveConstraint(constraintList);
		debugEnd(BmNames.RENAME_VARIABLES_DISJUNCTIVE);
		return result;
	}

	private EqConstraint<NODE> renameVariables(final EqConstraint<NODE> oldConstraint,
			final Map<Term, Term> substitutionMapping, final boolean inplace) {
		debugStart(BmNames.RENAME_VARIABLES);
		if (inplace) {
			mWeqCcManager.renameVariables(oldConstraint.getWeqCc(), substitutionMapping, true);
			debugEnd(BmNames.RENAME_VARIABLES);
			return oldConstraint;
		}
		final WeqCongruenceClosure<NODE> newWeqCc =
				mWeqCcManager.renameVariables(oldConstraint.getWeqCc(), substitutionMapping, false);
		final EqConstraint<NODE> result = getEqConstraint(newWeqCc, false);
		debugEnd(BmNames.RENAME_VARIABLES);
		return result;
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
		debugStart(BmNames.PROJECTAWAY);
		if (original.isBottom()) {
			debugEnd(BmNames.PROJECTAWAY);
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
		}
		WeqCongruenceClosure<NODE> newWeqCc = original.getWeqCc();
		for (final Term term : termsToProjectAway) {
			if (!getEqNodeAndFunctionFactory().hasNode(term)) {
				continue;
			}
			if (newWeqCc.isInconsistent(false)) {
				postProjectHelper(original, termsToProjectAway, getBottomConstraint());
				return getBottomConstraint();
			}

			// havoccing an element
			final NODE nodeToProjectAway = getEqNodeAndFunctionFactory().getExistingNode(term);
			newWeqCc = mWeqCcManager.projectAway(newWeqCc, nodeToProjectAway);

			if (newWeqCc.isInconsistent(false)) {
				postProjectHelper(original, termsToProjectAway, getBottomConstraint());
				return getBottomConstraint();
			}

			assert newWeqCc.sanityCheck();
		}
		result = getEqConstraint(newWeqCc, false);
		postProjectHelper(original, termsToProjectAway, result);
		return result;

	}

	private void postProjectHelper(final EqConstraint<NODE> original, final Collection<Term> termsToProjectAway,
			final EqConstraint<NODE> result) {
		assert VPDomainHelpers.constraintFreeOfVars(termsToProjectAway, result,
				getMgdScript().getScript()) : "resulting constraint still has at least one of the to-be-projected vars";

		if (mIsDebugMode) {
			mLogger.debug("projected variables " + termsToProjectAway + " from " + original.hashCode() + " result: "
					+ result);
		}

		debugEnd(BmNames.PROJECTAWAY);
	}

	public AbstractNodeAndFunctionFactory<NODE, Term> getEqNodeAndFunctionFactory() {
		return mEqNodeAndFunctionFactory;
	}

	// public EqDisjunctiveConstraint<NODE> getTopDisjunctiveConstraint() {
	// return mEmptyDisjunctiveConstraint;
	// }

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

	public Set<IProgramConst> getNonTheoryLiterals() {
		return mNonTheoryLiterals;
	}

	/**
	 *
	 * @param modifiable
	 *            return a modifiable, fresh constraint
	 * @return
	 */
	public EqDisjunctiveConstraint<NODE> getEmptyDisjunctiveConstraint(final boolean modifiable) {
		if (modifiable) {
			return getDisjunctiveConstraint(Collections.singleton(getEmptyConstraint(true)));
		}
		return mEmptyDisjunctiveConstraint;
	}

	public BenchmarkWithCounters getBenchmark() {
		return mBenchmark;
	}

	private static enum BmNames {

		PROJECTAWAY, UNFREEZE, ADD_EQUALITY, ADD_DISEQUALITY, ADD_WEAK_EQUALITY, CONJOIN, CONJOIN_DISJUNCTIVE, DISJOIN,
		DISJOIN_DISJUNCTIVE, RENAME_VARIABLES, RENAME_VARIABLES_DISJUNCTIVE;

		static String[] getNames() {
			final String[] result = new String[values().length];
			for (int i = 0; i < values().length; i++) {
				result[i] = values()[i].name();
			}
			return result;
		}
	}

	public WeqSettings getWeqSettings() {
		return mWeqCcManager.getSettings();
	}

	public EqDisjunctiveConstraint<NODE> closeIfNecessary(final EqDisjunctiveConstraint<NODE> resNotClosed) {
		final Collection<EqConstraint<NODE>> constraintList = new ArrayList<>();
		for (final EqConstraint<NODE> c : resNotClosed.getConstraints()) {
			constraintList.add(closeIfNecessary(c));
		}
		return getDisjunctiveConstraint(constraintList);
	}
}
