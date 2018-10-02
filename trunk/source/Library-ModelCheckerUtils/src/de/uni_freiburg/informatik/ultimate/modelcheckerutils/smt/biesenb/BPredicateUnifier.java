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

	private final IUltimateServiceProvider mServices;
	private final ManagedScript mMgdScript;
	private final Script mScript;
	private PredicateTrie<IPredicate> mPredicateTrie;
	private final IImplicationGraph<IPredicate> mImplicationGraph;
	private final BasicPredicateFactory mBasicPredicateFactory;
	private final IPredicate mTruePredicate;
	private final IPredicate mFalsePredicate;
	private final Collection<IPredicate> mPredicates;
	private final Set<IPredicate> mIntricatePredicate;
	private final IIcfgSymbolTable mSymbolTable;
	private int mRestructureWitnessCounter;
	
	private long implicationTime = 0;

	private final PredicateUnifierStatisticsGenerator mStatisticsTracker;

	public BPredicateUnifier(final IUltimateServiceProvider services, final ManagedScript script,
			final BasicPredicateFactory factory, final IIcfgSymbolTable symbolTable, final boolean useMap) {
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
		mPredicateTrie = new PredicateTrie<>(mMgdScript, mTruePredicate, mFalsePredicate, mSymbolTable);
		if(useMap) {
			mImplicationGraph = new ImplicationMap<>(mMgdScript, this, mFalsePredicate, mTruePredicate, true);
		} else {
			mImplicationGraph = new ImplicationGraph<>(mMgdScript, this, mFalsePredicate, mTruePredicate);
		}
		mPredicates.add(mTruePredicate);
		mPredicates.add(mFalsePredicate);
	}

	public BPredicateUnifier(final IUltimateServiceProvider services, final ILogger logger, final ManagedScript script,
			final BasicPredicateFactory factory, final IIcfgSymbolTable symbolTable, final boolean useMap) {
		this(services, script, factory, symbolTable, useMap);
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
		//TODO false or true
		final IPredicate pred = mBasicPredicateFactory.or(false, minimalDisjunction);
		for (final IPredicate p : mPredicates) {
			if (p.getFormula().equals(pred.getFormula())) {
				return p;
			}
		}
		IPredicate result = getOrConstructPredicate(pred);
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
		IPredicate result = getOrConstructPredicate(pred);
		return result;
	}

	@Override
	public String collectPredicateUnifierStatistics() {
		final StringBuilder builder = new StringBuilder();
		builder.append(PredicateUnifierStatisticsType.getInstance().prettyprintBenchmarkData(mStatisticsTracker));
		builder.append(" " + (implicationTime / 100)/10d + "s impTime " + mPredicateTrie.getDepth());
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
			LBool result = mMgdScript.checkSat(this);
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
		IPredicate tfPred = catchTrueOrFalse(predicate);
		if(tfPred != null) return tfPred;
		final IPredicate unifiedPredicate = mPredicateTrie.unifyPredicate(predicate);
		// Check if predicate is new to the unifier
		if (mPredicates.add(unifiedPredicate)) {
			long start = System.currentTimeMillis();
			mImplicationGraph.unifyPredicate(unifiedPredicate);
			implicationTime += System.currentTimeMillis() - start;
			mStatisticsTracker.incrementConstructedPredicates();
		} else {
			// Check syntactic or semantic match
			if (unifiedPredicate.getFormula().toString().equals(predicate.getFormula().toString())) {
				mStatisticsTracker.incrementSyntacticMatches();
			} else {
				mStatisticsTracker.incrementSemanticMatches();
			}
		}
		mStatisticsTracker.stopTime();
		return unifiedPredicate;
	}
	
	private IPredicate catchTrueOrFalse(IPredicate pred) {
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
		LBool equalsTrue = isDistinct(pred, mTruePredicate);
		if (equalsTrue == LBool.UNSAT) {
			mStatisticsTracker.incrementSemanticMatches();
			mStatisticsTracker.stopTime();
			return mTruePredicate;
		} else if (equalsTrue == LBool.UNKNOWN) {
			mIntricatePredicate.add(pred);
			return pred;
		}
		LBool equalsFalse = isDistinct(pred, mFalsePredicate);
		if(equalsFalse == LBool.UNSAT) {
			mStatisticsTracker.incrementSemanticMatches();
			mStatisticsTracker.stopTime();
			return mFalsePredicate;
		}else if (equalsFalse == LBool.UNKNOWN) {
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

	public String print(boolean trie, boolean graph) {
		StringBuilder sb = new StringBuilder();
		if(trie) {
			sb.append("Predicate Trie:\n" + mPredicateTrie.toString());
		}
		if(graph) {
			sb.append("Implication Graph:\n" + mImplicationGraph.toString());
		}
		return sb.toString();
	}

	@Override
	public IPredicate constructNewPredicate(Term term, Map<IPredicate, Validity> impliedPredicates,
			Map<IPredicate, Validity> expliedPredicates) {
		// TODO Auto-generated method stub
		return null;
	}

	/**
	 * under construction - do not use
	 */
//	@Override
//	public IPredicate constructNewPredicate(final Term term, final Map<IPredicate, Validity> impliedPredicates,
//			final Map<IPredicate, Validity> expliedPredicates) {
//		// TODO Find a way to exploit that we already know this term is unique.
//		return getOrConstructPredicate(term);
//	}
//	
//	public int restructurePredicateTrie() {
//		final int oldDepth = mPredicateTrie.getDepth();
//		// trie already has minimal depth (true and false are not in depth included)
//		if (oldDepth <= minDepth(mPredicates.size())) return 0;
//
//		TransitiveClosureIG<IPredicate> transitiveClosure = new TransitiveClosureIG<>(mImplicationGraph);
//
//		final Map<Witness, Pair<Witness, Witness>> witnessMap = new HashMap<>();
//		Map<Term, IPredicate> preds = new HashMap<>();
//		mRestructureWitnessCounter = 0;
//		Witness root = getWitnessInductive(transitiveClosure, witnessMap, preds);
//		final PredicateTrie<IPredicate> restructuredTrie =
//				new PredicateTrie<>(mMgdScript, mTruePredicate, mFalsePredicate, mSymbolTable);
//		restructuredTrie.fillTrie(root, witnessMap, preds);
//		if (oldDepth - restructuredTrie.getDepth() > 0) {
//			mPredicateTrie = restructuredTrie;
//		}
//		return oldDepth - mPredicateTrie.getDepth();
//	}
//
//	private Witness getWitnessInductive(final TransitiveClosureIG<IPredicate> transitiveClosure, 
//			final Map<Witness, Pair<Witness, Witness>> witnessMap, Map<Term, IPredicate> preds) {
//		// Find best vertex
//		float optimum = ((float) transitiveClosure.getVertices().size()) / 2;
//		float minDif = optimum;
//		ImplicationVertex<IPredicate> vertex = mImplicationGraph.getFalseVertex();
//		for (final ImplicationVertex<IPredicate> v : transitiveClosure.getVertices()) {
//			final float vCount = v.getDescendants().size() + 1;
//			if (vCount == optimum) {
//				vertex = v;
//				break;
//			} else if (Math.abs(optimum - vCount) < minDif) {
//				minDif = Math.abs(optimum - vCount);
//				vertex = v;
//			}
//		}
//		// Find model
//		mRestructureWitnessCounter += 1;
//		final Witness witness = new Witness(mRestructureWitnessCounter,
//				mPredicateTrie.getWitness(vertex.getPredicate(), getBranches(vertex)));
//		Witness trueWitness = null;
//		Witness falseWitness = null;
//
//		final TransitiveClosureIG<IPredicate> trueGraph = new TransitiveClosureIG<>(vertex, 
//				transitiveClosure.getDescendantsMapping().get(vertex), mImplicationGraph.getFalseVertex());
//		System.out.println("trueSide " + vertex + trueGraph.getVertices());
//		Set<ImplicationVertex<IPredicate>> tGVertices = trueGraph.getVertices();
//		if (tGVertices.size() > 3) {
//			trueWitness = getWitnessInductive(trueGraph, witnessMap, preds);
//		}else {
//			for(ImplicationVertex<IPredicate> v : tGVertices) {
//				Term t = v.getPredicate().getFormula();
//				if(!t.equals(mScript.term("false")) && !t.equals(mScript.term("true"))) {
//					Map<Term, Term> map = new HashMap<>();
//					map.put(t, null);
//					trueWitness = new Witness(-1 ,map);
//					preds.put(t, v.getPredicate());
//				}
//			}
//		}
//		transitiveClosure.removeDescendantsFromTC(vertex, mImplicationGraph.getTrueVertex());
//		transitiveClosure.removeVertex(vertex);
//		Set<ImplicationVertex<IPredicate>> fGVertices = transitiveClosure.getVertices();
//		System.out.println("falseSide " + vertex + transitiveClosure.getVertices().size());
//		if (fGVertices.size() > 3) {
//			falseWitness = getWitnessInductive(transitiveClosure, witnessMap, preds);
//		}else {
//			for(ImplicationVertex<IPredicate> v : fGVertices) {
//				Term t = v.getPredicate().getFormula();
//				if(!t.equals(mScript.term("false")) && !t.equals(mScript.term("true"))) {
//					Map<Term, Term> map = new HashMap<>();
//					map.put(t, null);
//					falseWitness = new Witness(-1, map);
//					preds.put(t, v.getPredicate());
//				}
//			}
//		}
//		witnessMap.put((witness), new Pair<>(trueWitness, falseWitness));
//		return witness;
//	}
//
//	private Set<IPredicate> getBranches(final ImplicationVertex<IPredicate> vertex) {
//		final Set<ImplicationVertex<IPredicate>> descendants = vertex.getDescendants();
//		final Set<ImplicationVertex<IPredicate>> included = vertex.getDescendants();
//		included.add(vertex);
//		final Set<IPredicate> branches = new HashSet<>();
//		for (final ImplicationVertex<IPredicate> d : included) {
//			d.getParents().forEach(p -> {
//				if (!descendants.contains(p)) {
//					branches.add(p.getPredicate());
//				}
//			});
//		}
//		branches.remove(vertex.getPredicate());
//		return branches;
//	}
//
//	private int minDepth(final int x) {
//		return (int) Math.ceil(Math.log(x) / Math.log(2) + 1);
//	}
}