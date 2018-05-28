/*
 * Copyright (C) 2016 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2016 Mostafa M.A. (mostafa.amin93@gmail.com)
 * Copyright (C) 2016 University of Freiburg
 *
 * This file is part of the ULTIMATE TreeAutomizer Plugin.
 *
 * The ULTIMATE TreeAutomizer Plugin is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TreeAutomizer Plugin is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TreeAutomizer Plugin. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TreeAutomizer Plugin, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TreeAutomizer Plugin grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.treeautomizer.graph;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.automata.tree.TreeRun;
import de.uni_freiburg.informatik.ultimate.lib.treeautomizer.HCSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.treeautomizer.HornClause;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.Substitution;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.PredicateUtils;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.PredicateUnifier;

/**
 * Computes a formula F from a TreeRun, i.e., a tree whose nodes are HornClauses (which contain HCTransFormulas).
 * The resulting formula is the result of applying resolution steps to the clauses according to the shape of the tree.
 * The formula F is used to compute "feasibility" of the TreeRun: If F is satisfiable, this means that our set of Horn
 * clauses is unsatisfiable, and the given TreeRun is a witness.
 *
 * The formula F is a kind of SSA form, it results from substituting variables in the "statements" of the HornClauses (
 * i.e. the part of a HornClause that is not an uninterpreted predicate).
 * The substitution that is computed is also necessary to translate the interpolants from the SMTSolver back into
 * predicates that TreeAutomizer uses for its interpolant automata.
 *
 * @author Mostafa M.A. (mostafa.amin93@gmail.com)
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 */
public class HCSSABuilder {

	private final TreeRun<HornClause, IPredicate> mInputTreeRun;
	private final ManagedScript mScript;
	private final PredicateUnifier mPredicateUnifier;

	private final HCSsa mResult;
	private int mIndexCounter = -1;

	/**
	 * stores the ssa-constants used by PredicateUtils.getIndexedConstant
	 */
	private final Map<String, Term> mIndexedConstants = new HashMap<>();
	private final Map<TreeRun<HornClause, IPredicate>, TreeRun<HornClause, SsaInfo>> mInputSubTreeToSsaSubtree =
			new HashMap<>();

	final HCSymbolTable mSymbolTable;

	/**
	 * Standard constructor, accepts all the input necessary for building the SSA.
	 * Triggers SSA construction. (result is obtained through getResult())
	 *
	 * @param inputTreeRun TreeRun from the emptiness check
	 * @param preCondition The precondition (the initial state's condition)
	 * @param postCondition The postcondition (the final state's condition)
	 * @param script The backend script
	 * @param predicateUnifier HornClause Predicate Factory
	 * @param hcSymbolTable
	 * */
	public HCSSABuilder(final TreeRun<HornClause, IPredicate> inputTreeRun, final IPredicate preCondition,
			final IPredicate postCondition, final ManagedScript script, final PredicateUnifier predicateUnifier,
			final HCSymbolTable hcSymbolTable) {
		mInputTreeRun = inputTreeRun;
		mScript = script;
		mSymbolTable = hcSymbolTable;
//		mTermTransferrer = new TermTransferrer(mScript.getScript());
//		mTransferToScriptNeeded = false;
//		mPreCondition = preCondition;
//		mPostCondition = postCondition;
//		mCounters = new HashMap<>();
//		mSubsMap = new HashMap<>();
		mPredicateUnifier = predicateUnifier;

//		mCurrentHcInVarVersion = new HashMap<>();
		mResult = buildSSA();

	}

	public HCSsa getSSA() {
		return mResult;
	}


//	private int getOrConstructIndex(final TreeRun<HornClause, IPredicate> tree) {
//		if (!mIdxMap.containsKey(tree)) {
//			++mCurrentIdx;
//			mIdxMap.put(tree, mCurrentIdx);
//		}
//		return mIdxMap.get(tree);
//	}


	/**
	 * Given a map from subtrees (TreeRuns) to interpolants in SSA-fomat, this method constructs a TreeRun that
	 * matches the input TreeRun of this class (in TreeAutomizer: the counterExample from the emptiness check)
	 * where the HCPredicates representing a Location/HCPredicateSymbol have been replaced by IPredicates representing
	 * the corresponding interpolant.
	 *
	 * @param interpolantsMap represents the tree interpolant as received from the SMT solver
	 * @return
	 */
	public TreeRun<HornClause, IPredicate> buildTreeRunWithBackVersionedInterpolants(
			final Map<TreeRun<HornClause, IPredicate>, Term> interpolantsMap) {
		return buildBackVersionedTreeRunRec(mInputTreeRun, interpolantsMap);
	}

	private TreeRun<HornClause, IPredicate> buildBackVersionedTreeRunRec(final TreeRun<HornClause, IPredicate> currentSubTree,
			final Map<TreeRun<HornClause, IPredicate>, Term> interpolantsMap) {
		final TreeRun<HornClause, SsaInfo> currentSsaSubtree = mInputSubTreeToSsaSubtree.get(currentSubTree);
		if (currentSsaSubtree == null) {
			// we're at a leaf
			return new TreeRun<>(mPredicateUnifier.getTruePredicate());
		}
		final Term currentInterpolantTermInSsa = interpolantsMap.get(currentSubTree);
		final HornClause currentHornClause = currentSubTree.getRootSymbol();

		// the interpolant term in terms of the TermVariabels of the HornClause
		final Term backSubstitutedTerm = new Substitution(mScript, currentSsaSubtree.getRoot().mBackSubstitution)
				.transform(currentInterpolantTermInSsa);

		final Map<Term, Term> hcvarSubstitution = new HashMap<>();
		for (int i = 0; !currentHornClause.isHeadFalse() &&  i < currentHornClause.getHeadPredicate().getArity(); i++) {
			throw new AssertionError("TODO: rework");
//			final TermVariable tvInHc = currentHornClause.getTermVariablesForHeadPred().get(i);
//			hcvarSubstitution.put(tvInHc, mSymbolTable.getHCOutVar(i, tvInHc.getSort()).getTermVariable());
		}
		// the interpolant term in terms of hcOutVars
		final Term backSubstitutedTermWithHcVars = new Substitution(mScript, hcvarSubstitution)
				.transform(backSubstitutedTerm);

		final IPredicate backSubstitutedPredicate = mPredicateUnifier
				.getOrConstructPredicate(backSubstitutedTermWithHcVars);

		final List<TreeRun<HornClause, IPredicate>> children = new ArrayList<>();
		for (int i = 0; i < currentSubTree.getChildren().size(); i++) {
			children.add(buildBackVersionedTreeRunRec(currentSubTree.getChildren().get(i), interpolantsMap));
		}

		return new TreeRun<HornClause, IPredicate>(backSubstitutedPredicate, currentHornClause, children);
	}

	private HCSsa buildSSA() {
		assert mInputTreeRun.getRootSymbol() != null;
		assert mInputTreeRun.getRoot() != null;

		// the empty list should work here, because there is no head predicate at the root..
		final TreeRun<HornClause, SsaInfo> resultTreeRun = buildSSArec(mInputTreeRun, Collections.emptyList());

		return new HCSsa(resultTreeRun);
	}

	private TreeRun<HornClause, SsaInfo> buildSSArec(final TreeRun<HornClause, IPredicate> inputTreeRun,
			final List<ApplicationTerm> headPredSsaConstants) {

		final HornClause currentHornClause = inputTreeRun.getRootSymbol();

		final SsaInfo ssaInfo = buildSsaInfo(inputTreeRun.getRootSymbol(), headPredSsaConstants);

		assert ssaInfo.mSubstitutionForBodyPred.size() == currentHornClause.getNoBodyPredicates();

		final List<TreeRun<HornClause, SsaInfo>> subTreeRuns = new ArrayList<>();
		for (int i = 0; i < currentHornClause.getNoBodyPredicates(); i++) {
			final TreeRun<HornClause, SsaInfo> subTreeRun =
					buildSSArec(inputTreeRun.getChildren().get(i), ssaInfo.mSubstitutionForBodyPred.get(i));
			subTreeRuns.add(subTreeRun);
		}

		final TreeRun<HornClause, SsaInfo> res;
			res = new TreeRun<>(ssaInfo, currentHornClause, subTreeRuns);
		mInputSubTreeToSsaSubtree.put(inputTreeRun, res);

		return res;
	}

	private SsaInfo buildSsaInfo(final HornClause rootSymbol, final List<ApplicationTerm> headPredConstants) {
		throw new AssertionError("TODO: rework");

//		final Map<Term, Term> substitution = new HashMap<>();
//
//
//		for (int i = 0; i < rootSymbol.getTermVariablesForHeadPred().size(); i++) {
//			substitution.put(rootSymbol.getTermVariablesForHeadPred().get(i), headPredConstants.get(i));
//		}
//
//		final List<List<ApplicationTerm>> substitutionForBodyPred = new ArrayList<>();
//
//		for (int i = 0; i < rootSymbol.getBodyPredicates().size(); i++) {
//			final List<ApplicationTerm> subsForCurrentBodyPred = new ArrayList<>();
//			for (int j = 0; j < rootSymbol.getBodyPredToTermVariables().get(i).size(); j++) {
//				final Term bptv = rootSymbol.getBodyPredToTermVariables().get(i).get(j);
//				if (substitution.keySet().contains(bptv)) {
//					// tv already in substitution because already present in head
//					subsForCurrentBodyPred.add((ApplicationTerm) substitution.get(bptv));
//				} else {
//					//
//					final ApplicationTerm fresh = getFreshConstant(bptv);
//					substitution.put(bptv, fresh);
//					subsForCurrentBodyPred.add(fresh);
//				}
//
//			}
//			assert subsForCurrentBodyPred.size() == rootSymbol.getBodyPredicates().get(i).getArity();
//			substitutionForBodyPred.add(Collections.unmodifiableList(subsForCurrentBodyPred));
//		}
//
//
//		/*
//		 *  the substituted formula has the ssa-renaming
//		 *  --> including the closing, i.e., constants instead of variables
//		 *  it contains fresh constants (unless all variabels from the head are unchanged in the body pos)
//		 */
//		final Term substitutedFormula = new Substitution(mScript, substitution).transform(rootSymbol.getFormula());
//
//		return new SsaInfo(rootSymbol, substitution, substitutedFormula, substitutionForBodyPred);
	}

	/**
	 * obtain a fresh ssa-constant for the given TermVariable, also takes care of declaring it.
	 * @param tv
	 * @return
	 */
	private ApplicationTerm getFreshConstant(final TermVariable tv) {
//		mScript.lock(this);
		final Term res = PredicateUtils.getIndexedConstant(tv.getName(), tv.getSort(), getFreshIndex(tv), mIndexedConstants,
				mScript.getScript());
//		mScript.unlock(this);
		return (ApplicationTerm) res;
	}


	private int getFreshIndex(final TermVariable tv) {
		return ++mIndexCounter;
	}



}

/**
 * Keeps the information about the SSA-substitution of one node in a TreeRun.
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 */
class SsaInfo {

	final HornClause mHornClause;
	final Map<Term, Term> mSubstitution;
	final Map<Term, Term> mBackSubstitution;
	final Term mSsaFormula;
	final List<List<ApplicationTerm>> mSubstitutionForBodyPred;

	/**
	 * constructs an empty SSaInfo (its fields should not be accessed..
	 */
	public SsaInfo() {
		mHornClause = null;
		mSubstitution = null;
		mBackSubstitution = null;
		mSsaFormula = null;
		mSubstitutionForBodyPred = null;
	}

	/**
	 *
	 * @param hornClause the HornClause we are building an SSA for at this node in the tree run
	 * @param substitution the ssa-substitution that is applied for the hornclause's formula
	 * @param substitutedFormula the hornclause's formula after substitution
	 * @param substitutionForBodyPred the ssa-constant for each position in each body pred of the hornclause
	 */
	public SsaInfo(final HornClause hornClause, final Map<Term, Term> substitution, final Term substitutedFormula,
			final List<List<ApplicationTerm>> substitutionForBodyPred) {
		mHornClause = hornClause;
		mSubstitution = Collections.unmodifiableMap(substitution);
		mSsaFormula = substitutedFormula;
		mSubstitutionForBodyPred = Collections.unmodifiableList(substitutionForBodyPred);

		final Map<Term, Term> backSubstitution = new HashMap<>();
		for (final Entry<Term, Term> en : substitution.entrySet()) {
			backSubstitution.put(en.getValue(), en.getKey());
		}
		mBackSubstitution = Collections.unmodifiableMap(backSubstitution);
	}
}
