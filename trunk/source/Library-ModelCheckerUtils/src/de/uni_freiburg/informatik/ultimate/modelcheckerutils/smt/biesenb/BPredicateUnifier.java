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
	private final PredicateTrie<IPredicate> mPredicateTrie;
	private final ImplicationGraph<IPredicate> mImplicationGraph;
	private final BasicPredicateFactory mBasicPredicateFactory;
	private final IPredicate mTruePredicate;
	private final IPredicate mFalsePredicate;
	private final Collection<IPredicate> mPredicates;
	private final PredicateCoverageChecker mCoverageChecker;
	private final IIcfgSymbolTable mSymbolTable;

	private final PredicateUnifierStatisticsGenerator mStatisticsTracker;

	public BPredicateUnifier(final IUltimateServiceProvider services, final ManagedScript script,
			final BasicPredicateFactory factory, final IIcfgSymbolTable symbolTable) {
		mServices = services;
		mMgdScript = script;
		mScript = mMgdScript.getScript();
		mBasicPredicateFactory = factory;
		mSymbolTable = symbolTable;
		mTruePredicate = factory.newPredicate(mScript.term("true"));
		mFalsePredicate = factory.newPredicate(mScript.term("false"));
		mPredicates = new HashSet<>();
		mStatisticsTracker = new PredicateUnifierStatisticsGenerator();
		mPredicateTrie = new PredicateTrie<>(mMgdScript, mTruePredicate, mFalsePredicate, mSymbolTable);
		mImplicationGraph = new ImplicationGraph<>(mMgdScript, mFalsePredicate, mTruePredicate);
		mCoverageChecker = new PredicateCoverageChecker(mImplicationGraph, this);

		mPredicates.add(mTruePredicate);
		mPredicates.add(mFalsePredicate);
	}

	/**
	 * @deprecated Does not work at the moment
	 */
	@Deprecated
	public Map<Map<Term, Term>, Pair<Map<Term, Term>, Map<Term, Term>>> restructurePredicateTrie() {
		final int oldDepth = mPredicateTrie.getDepth();
		// Empty trie
		if (oldDepth <= 0) {
			return new HashMap<>();
			// trie already has minimal depth (true and false are not in depth included)
			// if(oldDepth <= minDepth(mPredicates.size() - 2)) return new HashMap<>();
		}

		final Pair<ImplicationGraph<IPredicate>, Map<ImplicationVertex<IPredicate>, ImplicationVertex<IPredicate>>> copyPair =
				mImplicationGraph.createFullCopy();
		final ImplicationGraph<IPredicate> copy = copyPair.getFirst();

		// while(!every ModelVertex is determend)
		final Map<Map<Term, Term>, Pair<Map<Term, Term>, Map<Term, Term>>> witnesses = new HashMap<>();
		getWitnessInductive(copy, witnesses);
		// Add all predicates to the trie

		final PredicateTrie restructuredTrie =
				new PredicateTrie(mMgdScript, mTruePredicate, mFalsePredicate, mSymbolTable);
		if (oldDepth - mPredicateTrie.getDepth() > 0) {
			// mPredicateTrie = restructuredTrie;
		}
		return witnesses;
		// return oldDepth - mPredicateTrie.getDepth();
	}

	private Map<Term, Term> getWitnessInductive(final ImplicationGraph<IPredicate> graph,
			final Map<Map<Term, Term>, Pair<Map<Term, Term>, Map<Term, Term>>> witnesses) {
		// Find best vertex
		final int optimum = graph.getVertices().size() / 2;
		int minDif = optimum;
		ImplicationVertex<IPredicate> vertex = graph.getFalseVertex();
		for (final ImplicationVertex<IPredicate> v : graph.getVertices()) {
			final int vCount = v.getDescendants().size() + 1;
			if (vCount == optimum) {
				vertex = v;
				break;
			} else if (Math.abs(optimum - vCount) < minDif) {
				minDif = Math.abs(optimum - vCount);
				vertex = v;
			}
		}
		// Find model
		final Map<Term, Term> witness = mPredicateTrie.getWitness(vertex.getPredicate(), getBranches(vertex));

		Map<Term, Term> trueWitness = null;
		Map<Term, Term> falseWitness = null;

		final Set<ImplicationVertex<IPredicate>> trueSide = new HashSet<>();
		trueSide.add(vertex);
		final ImplicationGraph<IPredicate> trueGraph = graph.createSubCopy(trueSide, true).getFirst();
		if (trueGraph.getVertices().size() > 3) {
			trueWitness = getWitnessInductive(trueGraph, witnesses);
		}
		graph.removeAllImpliedVertices(vertex, true);
		graph.removeVertex(vertex);
		if (graph.getVertices().size() > 3) {
			falseWitness = getWitnessInductive(graph, witnesses);
		}
		witnesses.put(witness, new Pair<>(trueWitness, falseWitness));
		return witness;
	}

	private Set<IPredicate> getBranches(final ImplicationVertex vertex) {
		final Set<ImplicationVertex<IPredicate>> decendents = vertex.getDescendants();
		final Set<IPredicate> branches = new HashSet<>();
		for (final ImplicationVertex<IPredicate> d : decendents) {
			d.getParents().forEach(p -> {
				if (!decendents.contains(p)) {
					branches.add(p.getPredicate());
				}
			});
		}
		branches.remove(vertex.getPredicate());
		return branches;
	}

	private int minDepth(final int x) {
		return (int) Math.ceil(Math.log(x) / Math.log(2) + 1);
	}

	@Override
	public IPredicate getOrConstructPredicateForDisjunction(final Collection<IPredicate> disjunction) {
		for (final IPredicate d : disjunction) {
			if (!mPredicates.contains(d)) {
				throw new AssertionError("PredicateUnifier does not know the predicate " + d);
			}
		}
		final ImplicationGraph<IPredicate> copyGraph = mImplicationGraph.createFullCopy().getFirst();

		final Collection<IPredicate> checked = new HashSet<>();
		final Deque<ImplicationVertex<IPredicate>> childless = new HashDeque<>();
		childless.add(copyGraph.getTrueVertex());

		// remove predicates that imply other predicates of the collection
		while (!childless.isEmpty()) {
			final ImplicationVertex<IPredicate> next = childless.pop();
			if (disjunction.contains(next.getPredicate())) {
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
		for (final IPredicate c : conjunction) {
			if (!mPredicates.contains(c)) {
				throw new AssertionError("PredicateUnifier does not know the predicate " + c);
			}
		}
		final Collection<IPredicate> minimalConjunction =
				mImplicationGraph.removeImplyedVerticesFromCollection(conjunction);
		final IPredicate pred = mBasicPredicateFactory.and(minimalConjunction);
		for (final IPredicate p : mPredicates) {
			if (p.getFormula().equals(pred.getFormula())) {
				return p;
			}
		}
		return getOrConstructPredicate(pred);
	}

	@Override
	public String collectPredicateUnifierStatistics() {
		final StringBuilder builder = new StringBuilder();
		builder.append(PredicateUnifierStatisticsType.getInstance().prettyprintBenchmarkData(mStatisticsTracker));
		return builder.toString();
	}

	@Override
	public IPredicateCoverageChecker getCoverageRelation() {
		return mCoverageChecker;
	}

	@Override
	public IStatisticsDataProvider getPredicateUnifierBenchmark() {
		return mStatisticsTracker;
	}

	@Override
	public boolean isIntricatePredicate(final IPredicate pred) {
		return isDistinct(pred, mTruePredicate) == LBool.UNKNOWN || isDistinct(pred, mFalsePredicate) == LBool.UNKNOWN;
	}

	private LBool isDistinct(final IPredicate pred1, final IPredicate pred2) {
		mMgdScript.lock(this);
		mMgdScript.push(this, 1);
		final Term isDistinct = mMgdScript.term(this, "distinct", pred1.getClosedFormula(), pred2.getClosedFormula());
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
		mStatisticsTracker.incrementGetRequests();
		return getOrConstructPredicateInternal(term);
	}

	private IPredicate getOrConstructPredicateInternal(final Term term) {
		final Term commuNF = new CommuhashNormalForm(mServices, mScript).transform(term);
		final IPredicate predicate = mBasicPredicateFactory.newPredicate(commuNF);
		// catch terms equal to true of false
		if (mTruePredicate.getFormula().equals(commuNF)) {
			mStatisticsTracker.incrementSyntacticMatches();
			return mTruePredicate;
		} else if (mFalsePredicate.getFormula().equals(commuNF)) {
			mStatisticsTracker.incrementSyntacticMatches();
			return mFalsePredicate;
		} else if (isDistinct(predicate, mTruePredicate) == LBool.UNSAT) {
			mStatisticsTracker.incrementSemanticMatches();
			return mTruePredicate;
		} else if (isDistinct(predicate, mFalsePredicate) == LBool.UNSAT) {
			mStatisticsTracker.incrementSemanticMatches();
			return mFalsePredicate;
		}

		final IPredicate unifiedPredicate = mPredicateTrie.unifyPredicate(predicate);
		// Check if predicate is new to the unifier
		if (mPredicates.add(unifiedPredicate)) {
			mImplicationGraph.unifyPredicate(unifiedPredicate);
			mStatisticsTracker.incrementConstructedPredicates();
		} else {
			// Check syntactic or semantic match
			if (unifiedPredicate.getFormula().toString().equals(predicate.getFormula().toString())) {
				mStatisticsTracker.incrementSyntacticMatches();
			} else {
				mStatisticsTracker.incrementSemanticMatches();
			}
		}
		return unifiedPredicate;
	}

	@Override
	/**
	 * Returns the corresponding predicate. If there is no such predicate the predicate is added to the unifier and
	 * returned.
	 */
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

	@Override
	public String toString() {
		return mPredicateTrie.toString() + " " + mImplicationGraph.toString();
	}

	@Override
	public IPredicate constructNewPredicate(final Term term, final Map<IPredicate, Validity> impliedPredicates,
			final Map<IPredicate, Validity> expliedPredicates) {
		// TODO Find a way to exploit that we already know this term is unique.
		return getOrConstructPredicate(term);
	}
}