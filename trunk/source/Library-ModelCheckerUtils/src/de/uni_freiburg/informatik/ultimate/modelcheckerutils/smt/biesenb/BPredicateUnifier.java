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
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.IIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hoaretriple.IHoareTripleChecker.Validity;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.CommuhashNormalForm;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.BasicPredicateFactory;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicateCoverageChecker;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.PredicateUnifierStatisticsGenerator;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.PredicateUnifierStatisticsGenerator.PredicateUnifierStatisticsType;
import de.uni_freiburg.informatik.ultimate.util.datastructures.HashDeque;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;
import de.uni_freiburg.informatik.ultimate.util.statistics.IStatisticsDataProvider;

/**
 * Data structure that stores unique predicates and simplifies terms with the help of an implication tree
 *
 * @author ben.biesenbach@neptun.uni-freiburg.de
 */
public class BPredicateUnifier implements IPredicateUnifier {

	private static final boolean USE_MAP = true;
	private static final boolean USE_RESTRUCTURE = true;

	private final IUltimateServiceProvider mServices;
	private final ManagedScript mMgdScript;
	private final Script mScript;
	private final IImplicationGraph<IPredicate> mImplicationGraph;
	private final BasicPredicateFactory mBasicPredicateFactory;
	private final IPredicate mTruePredicate;
	private final IPredicate mFalsePredicate;
	private final Collection<IPredicate> mPredicates;
	private final Set<IPredicate> mIntricatePredicate;
	private final IIcfgSymbolTable mSymbolTable;
	private final PredicateUnifierStatisticsGenerator mStatisticsTracker;
	private final ILogger mLogger;

	private PredicateTrie<IPredicate> mPredicateTrie;

	// hack to prevent creating own statistics object (should be done instead of using this)
	private long mImplicationTime = 0;
	private int mDepthOffset;

	public BPredicateUnifier(final IUltimateServiceProvider services, final ILogger logger, final ManagedScript script,
			final BasicPredicateFactory factory, final IIcfgSymbolTable symbolTable) {
		mLogger = logger;
		mServices = services;
		mMgdScript = script;
		mScript = mMgdScript.getScript();
		mBasicPredicateFactory = factory;
		mSymbolTable = symbolTable;
		mTruePredicate = factory.newPredicate(mScript.term("true"));
		mFalsePredicate = factory.newPredicate(mScript.term("false"));
		mPredicates = new HashSet<>();
		mIntricatePredicate = new HashSet<>();
		mStatisticsTracker = new PredicateUnifierStatisticsGenerator();
		mPredicateTrie = new PredicateTrie<>(logger, services, mMgdScript, mTruePredicate, mFalsePredicate, factory, mSymbolTable);
		if (USE_MAP) {
			mImplicationGraph = new ImplicationMap<>(mMgdScript, this, mFalsePredicate, mTruePredicate, true);
		} else {
			mImplicationGraph = new ImplicationGraph<>(mMgdScript, this, mFalsePredicate, mTruePredicate);
		}
		mPredicates.add(mTruePredicate);
		mPredicates.add(mFalsePredicate);
		mDepthOffset = 0;
		logger.info("Initialized predicate-trie based predicate unifier");
	}

	@Override
	public IPredicate getOrConstructPredicateForDisjunction(final Collection<IPredicate> disjunction) {
		for (final IPredicate d : disjunction) {
			if (!mPredicates.contains(d)) {
				throw new AssertionError("PredicateUnifier does not know the predicate " + d);
			}
		}
		final Collection<IPredicate> minimalDisjunction =
				mImplicationGraph.removeImplyingVerticesFromCollection(disjunction);
		// TODO false or true
		final IPredicate pred = mBasicPredicateFactory.or(false, minimalDisjunction);
		for (final IPredicate p : mPredicates) {
			if (p.getFormula().equals(pred.getFormula())) {
				return p;
			}
		}
		final IPredicate result = getOrConstructPredicate(pred);
		return result;
	}

	@Override
	public IPredicate getOrConstructPredicateForConjunction(final Collection<IPredicate> conjunction) {
		for (final IPredicate c : conjunction) {
			if (!mPredicates.contains(c)) {
				throw new AssertionError("PredicateUnifier does not know the predicate " + c);
			}
		}
		final Collection<IPredicate> minimalConjunction =
				mImplicationGraph.removeImpliedVerticesFromCollection(conjunction);
		final IPredicate pred = mBasicPredicateFactory.and(minimalConjunction);
		for (final IPredicate p : mPredicates) {
			if (p.getFormula().equals(pred.getFormula())) {
				return p;
			}
		}
		final IPredicate result = getOrConstructPredicate(pred);
		return result;
	}

	@Override
	public String collectPredicateUnifierStatistics() {
		final StringBuilder builder = new StringBuilder();
		builder.append(PredicateUnifierStatisticsType.getInstance().prettyprintBenchmarkData(mStatisticsTracker));
		builder.append(" " + (mImplicationTime / 100) / 10d + "s impTime " + mPredicateTrie.getDepth());
		return builder.toString();
	}

	@Override
	public IPredicateCoverageChecker getCoverageRelation() {
		return mImplicationGraph;
	}

	@Override
	public IStatisticsDataProvider getPredicateUnifierBenchmark() {
		return mStatisticsTracker;
	}

	@Override
	public boolean isIntricatePredicate(final IPredicate pred) {
		return mIntricatePredicate.contains(pred);
	}

	private LBool isDistinct(final IPredicate pred1, final IPredicate pred2) {
		if (mMgdScript.isLocked()) {
			mMgdScript.requestLockRelease();
		}
		final Term isDistinct = mScript.term("distinct", pred1.getClosedFormula(), pred2.getClosedFormula());
		mMgdScript.lock(this);
		mMgdScript.push(this, 1);
		try {
			mMgdScript.assertTerm(this, isDistinct);
			final LBool result = mMgdScript.checkSat(this);
			return result;
		} finally {
			mMgdScript.pop(this, 1);
			mMgdScript.unlock(this);
		}
	}

	@Override
	public Set<IPredicate> cannibalize(final boolean splitNumericEqualities, final Term term) {
		final Term[] conjuncts = SmtUtils.cannibalize(mMgdScript, mServices, splitNumericEqualities, term);
		final Set<IPredicate> result = new HashSet<>(conjuncts.length);
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

	/**
	 * Returns the corresponding predicate for the term. If there is no such predicate a new predicate is constructed
	 * and returned.
	 */
	@Override
	public IPredicate getOrConstructPredicate(final Term term) {
		mStatisticsTracker.incrementGetRequests();
		return getOrConstructPredicateInternal(term);
	}

	private IPredicate getOrConstructPredicateInternal(final Term term) {
		mStatisticsTracker.continueTime();
		final Term commuNF = new CommuhashNormalForm(mServices, mScript).transform(term);
		final IPredicate predicate = mBasicPredicateFactory.newPredicate(commuNF);
		// catch terms equal to true of false
		final IPredicate tfPred = catchTrueOrFalse(predicate);
		if (tfPred != null) {
			return tfPred;
		}
		final IPredicate unifiedPredicate = mPredicateTrie.unifyPredicate(predicate);
		// Check if predicate is new to the unifier
		if (mPredicates.add(unifiedPredicate)) {
			final long start = System.currentTimeMillis();
			mImplicationGraph.unifyPredicate(unifiedPredicate);
			mImplicationTime += System.currentTimeMillis() - start;
			mStatisticsTracker.incrementConstructedPredicates();
		} else {
			// Check syntactic or semantic match
			if (unifiedPredicate.getFormula().toString().equals(predicate.getFormula().toString())) {
				mStatisticsTracker.incrementSyntacticMatches();
			} else {
				mStatisticsTracker.incrementSemanticMatches();
			}
		}

		if (false && USE_RESTRUCTURE) {
			final int oldDepth = mPredicateTrie.getDepth();
			if (oldDepth > (minDepth(mPredicates.size())) * 3 + mDepthOffset) {
				restructurePredicateTrie();
				final int newDepth = mPredicateTrie.getDepth();
				mDepthOffset = newDepth - minDepth(mPredicates.size());
				mLogger.info("--------PredicateTrie is restructured: " + "old depths: " + oldDepth + " new depth: "
						+ newDepth);
			}
		}
		mStatisticsTracker.stopTime();
		return unifiedPredicate;
	}

	private IPredicate catchTrueOrFalse(final IPredicate pred) {
		if (mTruePredicate.getFormula().equals(pred.getFormula())) {
			mStatisticsTracker.incrementSyntacticMatches();
			mStatisticsTracker.stopTime();
			return mTruePredicate;
		}
		if (mFalsePredicate.getFormula().equals(pred.getFormula())) {
			mStatisticsTracker.incrementSyntacticMatches();
			mStatisticsTracker.stopTime();
			return mFalsePredicate;
		}
		final LBool equalsTrue = isDistinct(pred, mTruePredicate);
		if (equalsTrue == LBool.UNSAT) {
			mStatisticsTracker.incrementSemanticMatches();
			mStatisticsTracker.stopTime();
			return mTruePredicate;
		} else if (equalsTrue == LBool.UNKNOWN) {
			mIntricatePredicate.add(pred);
			return pred;
		}
		final LBool equalsFalse = isDistinct(pred, mFalsePredicate);
		if (equalsFalse == LBool.UNSAT) {
			mStatisticsTracker.incrementSemanticMatches();
			mStatisticsTracker.stopTime();
			return mFalsePredicate;
		} else if (equalsFalse == LBool.UNKNOWN) {
			mIntricatePredicate.add(pred);
			return pred;
		}
		return null;
	}

	/**
	 * Returns the corresponding predicate. If there is no such predicate the predicate is added to the unifier and
	 * returned.
	 */
	@Override
	public IPredicate getOrConstructPredicate(final IPredicate predicate) {
		if (mPredicates.contains(predicate)) {
			return predicate;
		}
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

	public String print(final boolean trie, final boolean graph) {
		final StringBuilder sb = new StringBuilder();
		if (trie) {
			sb.append("Predicate Trie:\n" + mPredicateTrie.toString());
		}
		if (graph) {
			sb.append("Implication Graph:\n" + mImplicationGraph.toString());
		}
		return sb.toString();
	}

	@Override
	public IPredicate constructNewPredicate(final Term term, final Map<IPredicate, Validity> impliedPredicates,
			final Map<IPredicate, Validity> expliedPredicates) {
		// TODO Find a way to exploit that we already know this term is unique.
		return getOrConstructPredicate(term);
	}

	public boolean restructurePredicateTrie() {
		final int oldDepth = mPredicateTrie.getDepth();
		// trie already has minimal depth (true and false are not in depth included)
		if (oldDepth <= minDepth(mPredicates.size())) {
			return false;
		}
		ImplicationMap<IPredicate> map;
		if (mImplicationGraph instanceof ImplicationMap) {
			map = (ImplicationMap<IPredicate>) mImplicationGraph;
		} else {
			throw new UnsupportedOperationException("restructure only possible with ImplicationMap");
		}

		// restructure
		// remove true and false, as they are not included in the predicate trie
		final Map<IPredicate, Set<IPredicate>> descendantsMap = new HashMap<>();
		map.getDescendantsMap().entrySet().forEach(d -> descendantsMap.put(d.getKey(), new HashSet<>(d.getValue())));
		descendantsMap.remove(mFalsePredicate);
		descendantsMap.remove(mTruePredicate);
		descendantsMap.keySet().forEach(d -> descendantsMap.get(d).remove(mTruePredicate));
		final Map<IPredicate, Set<IPredicate>> ancestorsMap = new HashMap<>();
		map.getAncestorsMap().entrySet().forEach(a -> ancestorsMap.put(a.getKey(), new HashSet<>(a.getValue())));
		ancestorsMap.remove(mFalsePredicate);
		ancestorsMap.remove(mTruePredicate);
		ancestorsMap.keySet().forEach(a -> ancestorsMap.get(a).remove(mFalsePredicate));

		final Map<RestructureHelperObject, Pair<RestructureHelperObject, RestructureHelperObject>> witnessMap =
				new HashMap<>();

		final RestructureHelperObject root = getWitnessInductive(descendantsMap, ancestorsMap, witnessMap);

		final PredicateTrie<IPredicate> restructuredTrie =
				new PredicateTrie<>(mLogger, mServices, mMgdScript, mTruePredicate, mFalsePredicate, mBasicPredicateFactory, mSymbolTable);
		restructuredTrie.fillTrie(root, witnessMap);
		if (oldDepth - restructuredTrie.getDepth() > 0) {
			mPredicateTrie = restructuredTrie;
			return true;
		}
		return false;
	}

	private RestructureHelperObject getWitnessInductive(final Map<IPredicate, Set<IPredicate>> descendantsMap,
			final Map<IPredicate, Set<IPredicate>> ancestorsMap,
			final Map<RestructureHelperObject, Pair<RestructureHelperObject, RestructureHelperObject>> witnessMap) {
		// get witnessSet to split predicates in two groups
		final Pair<IPredicate, IPredicate> pivot = getPivot(descendantsMap, ancestorsMap);
		final Term distinct =
				mScript.term("and", pivot.getFirst().getFormula(), mScript.term("not", pivot.getSecond().getFormula()));

		final RestructureHelperObject witness = new RestructureHelperObject(mPredicateTrie.getWitness(distinct), null);

		final Pair<Set<IPredicate>, Set<IPredicate>> split =
				splitPredicates(witness, pivot, descendantsMap, ancestorsMap);

		RestructureHelperObject trueWitness = null;
		RestructureHelperObject falseWitness = null;

		// call function inductively until all predicates are sorted
		final Pair<Map<IPredicate, Set<IPredicate>>, Map<IPredicate, Set<IPredicate>>> trueSide =
				prepareSubGraph(split.getFirst(), descendantsMap, ancestorsMap);
		if (trueSide.getFirst().size() == 1) {
			trueWitness = new RestructureHelperObject(-1, null, trueSide.getFirst().keySet().iterator().next());
		} else {
			trueWitness = getWitnessInductive(trueSide.getFirst(), trueSide.getSecond(), witnessMap);
		}
		final Pair<Map<IPredicate, Set<IPredicate>>, Map<IPredicate, Set<IPredicate>>> falseSide =
				prepareSubGraph(split.getSecond(), descendantsMap, ancestorsMap);
		if (falseSide.getFirst().size() == 1) {
			falseWitness = new RestructureHelperObject(-1, null, falseSide.getFirst().keySet().iterator().next());
		} else {
			falseWitness = getWitnessInductive(falseSide.getFirst(), falseSide.getSecond(), witnessMap);
		}
		witnessMap.put((witness), new Pair<>(trueWitness, falseWitness));
		return witness;
	}

	private Pair<Map<IPredicate, Set<IPredicate>>, Map<IPredicate, Set<IPredicate>>> prepareSubGraph(
			final Set<IPredicate> preds, final Map<IPredicate, Set<IPredicate>> descendantsMap,
			final Map<IPredicate, Set<IPredicate>> ancestorsMap) {
		final Map<IPredicate, Set<IPredicate>> newDescendantsMap = new HashMap<>();
		for (final IPredicate pred : preds) {
			newDescendantsMap.put(pred, new HashSet<>(descendantsMap.get(pred)));
			for (final IPredicate old : descendantsMap.get(pred)) {
				if (!preds.contains(old)) {
					newDescendantsMap.get(pred).remove(old);
				}
			}
		}
		final Map<IPredicate, Set<IPredicate>> newAncestersMap = new HashMap<>();
		for (final IPredicate pred : preds) {
			newAncestersMap.put(pred, new HashSet<>(ancestorsMap.get(pred)));
			for (final IPredicate old : ancestorsMap.get(pred)) {
				if (!preds.contains(old)) {
					newAncestersMap.get(pred).remove(old);
				}
			}
		}
		return new Pair<>(newDescendantsMap, newAncestersMap);
	}

	private Pair<Set<IPredicate>, Set<IPredicate>> splitPredicates(final RestructureHelperObject witness,
			final Pair<IPredicate, IPredicate> pivot, final Map<IPredicate, Set<IPredicate>> descendantsMap,
			final Map<IPredicate, Set<IPredicate>> ancestorsMap) {

		final Deque<IPredicate> toCheck = new HashDeque<>();
		toCheck.addAll(descendantsMap.keySet());
		final Set<IPredicate> included = new HashSet<>(descendantsMap.get(pivot.getFirst()));
		included.add(pivot.getFirst());
		final Set<IPredicate> excluded = new HashSet<>(ancestorsMap.get(pivot.getSecond()));
		excluded.add(pivot.getSecond());
		excluded.removeAll(included);
		toCheck.removeAll(included);
		toCheck.removeAll(excluded);

		while (!toCheck.isEmpty()) {
			final IPredicate current = toCheck.pop();
			if (mPredicateTrie.fulfillsPredicate(current, witness.getWitness())) {
				included.add(current);
				included.addAll(descendantsMap.get(current));
				toCheck.removeAll(descendantsMap.get(current));
			} else {
				excluded.add(current);
				excluded.addAll(ancestorsMap.get(current));
				toCheck.removeAll(ancestorsMap.get(current));
			}
		}
		return new Pair<>(included, excluded);
	}

	private Pair<IPredicate, IPredicate> getPivot(final Map<IPredicate, Set<IPredicate>> descendantsMap,
			final Map<IPredicate, Set<IPredicate>> ancestorsMap) {
		assert (!descendantsMap.isEmpty() && !ancestorsMap.isEmpty());
		final float optimum = ((float) descendantsMap.keySet().size()) / 2;
		float minDif = optimum;
		IPredicate pivotIn = null;
		// find pivotIn
		for (final IPredicate pred : descendantsMap.keySet()) {
			final float vCount = descendantsMap.get(pred).size() + 1;
			if (vCount == optimum) {
				pivotIn = pred;
				break;
			} else if (Math.abs(optimum - vCount) < minDif) {
				minDif = Math.abs(optimum - vCount);
				pivotIn = pred;
			}
		}
		// update ancestors
		final Map<IPredicate, Set<IPredicate>> ancestors = new HashMap<>();
		for (final Map.Entry<IPredicate, Set<IPredicate>> ancestor : ancestorsMap.entrySet()) {
			ancestors.put(ancestor.getKey(), new HashSet<>(ancestor.getValue()));
		}
		for (final IPredicate pivotDescendants : descendantsMap.get(pivotIn)) {
			for (final IPredicate descendants : descendantsMap.get(pivotDescendants)) {
				ancestors.get(descendants).remove(pivotDescendants);
			}
		}
		for (final IPredicate pivotDescendants : descendantsMap.get(pivotIn)) {
			ancestors.remove(pivotDescendants);
		}
		ancestors.remove(pivotIn);
		minDif = optimum;
		// find pivotOut
		IPredicate pivotOut = null;
		for (final Entry<IPredicate, Set<IPredicate>> pred : ancestors.entrySet()) {
			final float vCount = pred.getValue().size() + 1;
			if (vCount == optimum) {
				pivotOut = pred.getKey();
				break;
			} else if (Math.abs(optimum - vCount) < minDif) {
				minDif = Math.abs(optimum - vCount);
				pivotOut = pred.getKey();
			}
		}
		return new Pair<>(pivotIn, pivotOut);
	}

	private int minDepth(final int x) {
		return (int) Math.ceil(Math.log(x) / Math.log(2) + 1);
	}
}