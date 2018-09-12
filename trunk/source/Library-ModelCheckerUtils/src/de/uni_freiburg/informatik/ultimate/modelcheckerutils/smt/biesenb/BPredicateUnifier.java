/*
 * Copyright (C) 2018 Ben Biesenbach (ben.biesenbach@neptun.uni-freiburg.de)
 * Copyright (C) 2018 University of Freiburg
 *
 * This file is part of the ULTIMATE ModelCheckerUtilsTest Library.
 *
 * The ULTIMATE ModelCheckerUtilsTest Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE ModelCheckerUtilsTest Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ModelCheckerUtilsTest Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ModelCheckerUtilsTest Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE ModelCheckerUtilsTest Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.biesenb;

import java.util.Collection;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.BasicPredicateFactory;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicateCoverageChecker;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.util.datastructures.HashDeque;
import de.uni_freiburg.informatik.ultimate.util.statistics.IStatisticsDataProvider;

/**
 * Data structure that stores unique predicates and simplifies terms with the help of an implication tree
 *
 * @author ben.biesenbach@neptun.uni-freiburg.de
 */
public class BPredicateUnifier implements IPredicateUnifier {

	private final IUltimateServiceProvider mServices;
	private final ManagedScript mMgdScript;
	private final Script mScript;
	private final PredicateTrie<IPredicate> mPredicateTrie;
	private final ImplicationGraph<IPredicate> mImplicationGraph;
	private final BasicPredicateFactory mBasicPredicateFactory;
	private final IPredicate mTruePredicate;
	private final IPredicate mFalsePredicate;
	private final Collection<IPredicate> mPredicates;
	private final PredicateCoverageChecker mConverageChecker;

	public BPredicateUnifier(final IUltimateServiceProvider services, final ManagedScript script,
			final BasicPredicateFactory factory) {
		mServices = services;
		mMgdScript = script;
		mScript = mMgdScript.getScript();
		mBasicPredicateFactory = factory;
		mTruePredicate = factory.newPredicate(mScript.term("true"));
		mFalsePredicate = factory.newPredicate(mScript.term("false"));
		mPredicates = new HashSet<>();
		mPredicateTrie = new PredicateTrie<>(mMgdScript);
		mImplicationGraph = new ImplicationGraph<>(mMgdScript, mFalsePredicate, mTruePredicate);
		mConverageChecker = new PredicateCoverageChecker(mImplicationGraph);
		
		mPredicates.add(mTruePredicate);
		mPredicates.add(mFalsePredicate);
	}

	@Override
	public IPredicate getOrConstructPredicateForDisjunction(final Collection<IPredicate> disjunction) {
		final Collection<IPredicate> unifiedDisjunction = mPredicateTrie.unifyPredicateCollection(disjunction);

		final ImplicationGraph<IPredicate> copyGraph = mImplicationGraph.createFullCopy().getFirst();

		final Collection<IPredicate> checked = new HashSet<>();
		final Deque<ImplicationVertex<IPredicate>> childless = new HashDeque<>();
		childless.add(copyGraph.getTrueVertex());

		// remove predicates that imply other predicates of the collection
		while (!childless.isEmpty()) {
			final ImplicationVertex<IPredicate> next = childless.pop();
			if (unifiedDisjunction.contains(next.getPredicate())) {
				checked.add(next.getPredicate());
				copyGraph.removeAllVerticesImplying(next);
			} else {
				for (final ImplicationVertex<IPredicate> parent : next.getParents()) {
					parent.removeChild(next);
					if (parent.getChildren().isEmpty()) {
						childless.add(parent);
					}
				}
			}
		}
		return getOrConstructPredicate(mBasicPredicateFactory.or(false, checked));
	}

	@Override
	public IPredicate getOrConstructPredicateForConjunction(final Collection<IPredicate> conjunction) {
		final Collection<IPredicate> unifiedConjunction = mPredicateTrie.unifyPredicateCollection(conjunction);
		final Collection<IPredicate> minimalConjunction =
				mImplicationGraph.removeImplyedVerticesFromCollection(unifiedConjunction);
		return getOrConstructPredicate(mBasicPredicateFactory.and(minimalConjunction));
	}

	@Override
	public String collectPredicateUnifierStatistics() {
		return mPredicateTrie.toString() + mImplicationGraph.toString();
	}

	@Override
	public IPredicateCoverageChecker getCoverageRelation() {
		return mConverageChecker;
	}

	@Override
	public IStatisticsDataProvider getPredicateUnifierBenchmark() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public boolean isIntricatePredicate(final IPredicate pred) {
		return (isDistinct(pred, mTruePredicate) == LBool.UNKNOWN
				|| isDistinct(pred, mFalsePredicate) == LBool.UNKNOWN);
	}

	private LBool isDistinct(final IPredicate pred1, final IPredicate pred2) {
		final Term isDistinct = mMgdScript.term(this, "distinct", pred1.getClosedFormula(), pred2.getClosedFormula());
		mMgdScript.lock(this);
		mMgdScript.push(this, 1);
		try {
			mMgdScript.assertTerm(this, isDistinct);
			return mMgdScript.checkSat(this);
		} finally {
			mMgdScript.pop(this, 1);
			mMgdScript.unlock(this);
		}
	}

	@Override
	public Set<IPredicate> cannibalize(final boolean splitNumericEqualities, final Term term) {
		final Term[] conjuncts = SmtUtils.cannibalize(mMgdScript, mServices, splitNumericEqualities, term);
		final Set<IPredicate> result = new HashSet<>();
		for (final Term conjunct : conjuncts) {
			final IPredicate predicate = getOrConstructPredicate(conjunct);
			result.add(predicate);
		}
		return result;
	}

	@Override
	public Set<IPredicate> cannibalizeAll(final boolean splitNumericEqualities,
			final Collection<IPredicate> predicates) {
		final Set<IPredicate> result = new HashSet<>();
		for (final IPredicate predicate : predicates) {
			result.addAll(cannibalize(splitNumericEqualities, predicate.getFormula()));
		}
		return result;
	}

	@Override
	/**
	 * Returns the corresponding predicate for the term. If there is no such predicate a new predicate is constructed
	 * and returned.
	 */
	public IPredicate getOrConstructPredicate(final Term term) {
		final IPredicate predicate = mBasicPredicateFactory.newPredicate(term);
		if (isDistinct(predicate, mTruePredicate) == LBool.UNSAT) {
			return mTruePredicate;
		} else if (isDistinct(predicate, mFalsePredicate) == LBool.UNSAT) {
			return mFalsePredicate;
		}
		final IPredicate unifiedPredicate = mPredicateTrie.unifyPredicate(predicate);
		// Check if predicate is new to the unifier
		if (unifiedPredicate == predicate) {
			mImplicationGraph.unifyPredicate(predicate);
			mPredicates.add(predicate);
		}
		return unifiedPredicate;
	}

	@Override
	/**
	 * Returns the corresponding predicate. If there is no such predicate the predicate is added to the unifier and
	 * returned.
	 */
	public IPredicate getOrConstructPredicate(final IPredicate predicate) {
		return getOrConstructPredicate(predicate.getFormula());
	}

	@Override
	public boolean isRepresentative(final IPredicate pred) {
		return mPredicates.contains(pred);
	}

	@Override
	public BasicPredicateFactory getPredicateFactory() {
		return mBasicPredicateFactory;
	}

	@Override
	public IPredicate getTruePredicate() {
		return mTruePredicate;
	}

	@Override
	public IPredicate getFalsePredicate() {
		return mFalsePredicate;
	}

}