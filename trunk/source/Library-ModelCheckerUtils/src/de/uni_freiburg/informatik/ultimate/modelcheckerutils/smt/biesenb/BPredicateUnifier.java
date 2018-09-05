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

import java.util.ArrayList;
import java.util.Collection;
import java.util.Deque;
import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.linearterms.BinaryNumericRelation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.linearterms.BinaryRelation.NoRelationOfThisKindException;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.linearterms.BinaryRelation.RelationSymbol;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.normalforms.CnfTransformer;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.BasicPredicateFactory;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicateCoverageChecker;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.util.datastructures.HashDeque;
import de.uni_freiburg.informatik.ultimate.util.statistics.IStatisticsDataProvider;

public class BPredicateUnifier implements IPredicateUnifier{
	
	private IUltimateServiceProvider mServices;
	private ManagedScript mMgdScript;
	private Script mScript;
	private PredicateTrie<IPredicate> mPredicateTrie;
	private ImplicationGraph<IPredicate> mImplicationGraph;
	private BasicPredicateFactory mBasicPredicateFactory;
	private IPredicate mTruePredicate;
	private IPredicate mFalsePredicate;
	private final Collection<IPredicate> mPredicates;
	
	/**
	 * Data structure that stores unique predicates and simplifies terms with the help of an implication tree 
	 * 
	 * @author ben.biesenbach@neptun.uni-freiburg.de
	 */
	public BPredicateUnifier (final IUltimateServiceProvider services, final ManagedScript script, final BasicPredicateFactory factory) {
		mServices = services;
		mMgdScript = script;
		mScript = mMgdScript.getScript();
		mBasicPredicateFactory = factory;
		mTruePredicate = factory.newPredicate(mScript.term("true"));
		mFalsePredicate = factory.newPredicate(mScript.term("false"));
		mPredicates = new HashSet<>();
		mPredicates.add(mTruePredicate);
		mPredicates.add(mFalsePredicate);
		mPredicateTrie = new PredicateTrie<>(mMgdScript);
		mImplicationGraph = new ImplicationGraph<>(mMgdScript, mFalsePredicate, mTruePredicate);
	}

	@Override
	public IPredicate getOrConstructPredicateForDisjunction(final Collection<IPredicate> disjunction) {
		Collection<IPredicate> unifiedDisjunction = mPredicateTrie.unifyPredicateCollection(disjunction);

		ImplicationGraph<IPredicate> copyGraph = mImplicationGraph.createFullCopy().getFirst();
		
		Collection<IPredicate> checked = new HashSet<>();
		Deque<ImplicationVertex<IPredicate>> childless = new HashDeque<>();
		childless.add(copyGraph.getTrueVertex());
		
		// remove predicates that imply other predicates of the collection
		while(!childless.isEmpty()) {
			ImplicationVertex<IPredicate> next = childless.pop();
			if(unifiedDisjunction.contains(next.getPredicate())) {	
				checked.add(next.getPredicate());
				copyGraph.removeAllVerticesImplying(next);
			} else {
				for(ImplicationVertex<IPredicate> parent : next.getParents()) {
					parent.removeChild(next);
					if(parent.getChildren().isEmpty()) {
						childless.add(parent);
					}
				}
			}
		}
		return getOrConstructPredicate(mBasicPredicateFactory.or(false, checked));
	}

	@Override
	public IPredicate getOrConstructPredicateForConjunction(final Collection<IPredicate> conjunction) {
		Collection<IPredicate> unifiedConjunction = mPredicateTrie.unifyPredicateCollection(conjunction);
		Collection<IPredicate> minimalConjunction = mImplicationGraph.removeImplyedVerticesFromCollection(unifiedConjunction);
		return getOrConstructPredicate(mBasicPredicateFactory.and(minimalConjunction));
	}

	@Override
	public String collectPredicateUnifierStatistics() {
		return mPredicateTrie.toString() + mImplicationGraph.toString();
	}
	
	@Override
	public IPredicateCoverageChecker getCoverageRelation() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public IStatisticsDataProvider getPredicateUnifierBenchmark() {
		// TODO Auto-generated method stub
		return null;
	}
	
	@Override
	public boolean isIntricatePredicate(final IPredicate pred) {
		return (isDistinct(pred, mTruePredicate) == LBool.UNKNOWN || isDistinct(pred, mFalsePredicate) == LBool.UNKNOWN);
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
	public Set<IPredicate> cannibalize(boolean splitNumericEqualities, Term term) {
		final Set<IPredicate> result = new HashSet<>();
		final Term cnf = new CnfTransformer(mMgdScript, mServices).transform(term);
		Term[] conjuncts;
		if(splitNumericEqualities) {
			conjuncts = SmtUtils.getConjuncts(cnf);
		} else {
			conjuncts = splitNumericEqualities(SmtUtils.getConjuncts(cnf));
		}
		for (final Term conjunct : conjuncts) {
			final IPredicate predicate = getOrConstructPredicate(conjunct);
			result.add(predicate);
		}
		//TODO why not remove the implyedVertices?
		//return (Set<IPredicate>) mImplicationGraph.removeImplyedVerticesFromCollection(result);
		
		return result;
	}
	
	private Term[] splitNumericEqualities(final Term[] conjuncts) {
		final ArrayList<Term> result = new ArrayList<>(conjuncts.length * 2);
		for (final Term conjunct : conjuncts) {
			try {
				final BinaryNumericRelation bnr = new BinaryNumericRelation(conjunct);
				if (bnr.getRelationSymbol() == RelationSymbol.EQ) {
					final Term leq = mScript.term("<=", bnr.getLhs(), bnr.getRhs());
					result.add(leq);
					final Term geq = mScript.term(">=", bnr.getLhs(), bnr.getRhs());
					result.add(geq);
				} else {
					result.add(conjunct);
				}
			} catch (final NoRelationOfThisKindException e) {
				result.add(conjunct);
			}
		}
		return result.toArray(new Term[result.size()]);
	}
	
	@Override
	public Set<IPredicate> cannibalizeAll(boolean splitNumericEqualities, Collection<IPredicate> predicates) {
		final Set<IPredicate> result = new HashSet<>();
		for (final IPredicate predicate : predicates) {
			result.addAll(cannibalize(splitNumericEqualities, predicate.getFormula()));
		}
		return result;
	}
	
	@Override
	/**
	 * Returns the corresponding predicate for the term. 
	 * If there is no such predicate a new predicate is constructed and returned.
	 */
	public IPredicate getOrConstructPredicate(final Term term) {
		IPredicate predicate = mBasicPredicateFactory.newPredicate(term);
		if(isDistinct(predicate, mTruePredicate) == LBool.UNSAT) return mTruePredicate;
		else if(isDistinct(predicate, mFalsePredicate) == LBool.UNSAT) return mFalsePredicate;
		IPredicate unifiedPredicate = mPredicateTrie.unifyPredicate(predicate);
		//Check if predicate is new to the unifier
		if(unifiedPredicate == predicate) {
			mImplicationGraph.unifyPredicate(predicate);
			mPredicates.add(predicate);
		}
		return unifiedPredicate;
	}
	
	@Override
	/**
	 * Returns the corresponding predicate.
	 * If there is no such predicate the predicate is added to the unifier and returned.
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