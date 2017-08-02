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
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.automata.tree.TreeRun;
import de.uni_freiburg.informatik.ultimate.lib.treeautomizer.HCInVar;
import de.uni_freiburg.informatik.ultimate.lib.treeautomizer.HCOutVar;
import de.uni_freiburg.informatik.ultimate.lib.treeautomizer.HornClause;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.MultiElementCounter;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.Substitution;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.TermTransferrer;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.PredicateUtils;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.PredicateUnifier;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap2;

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

	private final TreeRun<HornClause, IPredicate> mTreeRun;
	private final IPredicate mPostCondition;
	private final IPredicate mPreCondition;
	private final ManagedScript mScript;
	private final boolean mTransferToScriptNeeded;
	private final PredicateUnifier mPredicateUnifier;

	private final HCSsa mResult;

	protected final Map<Term, HCOutVar> mConstants2HCOutVar = new HashMap<>();
	private final TermTransferrer mTermTransferrer;
	private final MultiElementCounter<TermVariable> mConstForTvCounter = new MultiElementCounter<>();

	/**
	 * When we match the outVars of a HornClause H1 to the inVars of a HornClause H2, (H1 is the child of H2 in the 
	 *  TreeRun), the matching depends on 
	 *  - the child index of H1, i.e., the i, in "H1 is the i-th child of H2), called PredPos
	 *  - the index of the variable in the predicate, called argPos
	 */
	private final Map<HCInVar, Term> mCurrentHcInVarVersion;


	private final NestedMap2<HCInVar, Integer, Term> mIndexedVarRepresentative = new NestedMap2<>();
	private final Map<TreeRun<HornClause, IPredicate>, VariableVersioneer> mSubsMap;

	private final Map<Term, Integer> mCounters;
	private int mCurrentTree = -1;
	private final Map<String, Term> mIndexedConstants = new HashMap<>();

	private final Map<TreeRun<HornClause, IPredicate>, Integer> mIdxMap = new HashMap<>();
	private int mCurrentIdx;
	
	/**
	 * Standard constructor, accepts all the input necessary for building the SSA.
	 * Triggers SSA construction. (result is obtained through getResult())
	 * 
	 * @param trace TreeRun of the given traces
	 * @param preCondition The precondition (the initial state's condition)
	 * @param postCondition The postcondition (the final state's condition)
	 * @param script The backend script
	 * @param predicateUnifier HornClause Predicate Factory
	 * */
	public HCSSABuilder(final TreeRun<HornClause, IPredicate> trace, final IPredicate preCondition,
			final IPredicate postCondition, final ManagedScript script, final PredicateUnifier predicateUnifier) {
		mTreeRun = trace;
		mScript = script;
		mTermTransferrer = new TermTransferrer(mScript.getScript());
		mTransferToScriptNeeded = false;
		mPreCondition = preCondition;
		mPostCondition = postCondition;
		mCounters = new HashMap<>();
		mSubsMap = new HashMap<>();
		mPredicateUnifier = predicateUnifier;

		mCurrentHcInVarVersion = new HashMap<>();
		mResult = buildSSA();

	}

	public HCSsa getSSA() {
		return mResult;
	}


	private int getOrConstructIndex(final TreeRun<HornClause, IPredicate> tree) {
		if (!mIdxMap.containsKey(tree)) {
			++mCurrentIdx;
			mIdxMap.put(tree, mCurrentIdx);
		}
		return mIdxMap.get(tree);
	}
	
	
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
		final Map<TreeRun<HornClause, IPredicate>, IPredicate> backVersionedInterpolantsMap = new HashMap<>();
		for (Entry<TreeRun<HornClause, IPredicate>, Term> en : interpolantsMap.entrySet()) {
			VariableVersioneer versioneer = mSubsMap.get(en.getKey());
			assert versioneer != null;
			backVersionedInterpolantsMap.put(en.getKey(), versioneer.backVersion(en.getValue()));
			assert backVersionedInterpolantsMap.get(en.getKey()) != null;
		}
		
		return mTreeRun.reconstructViaSubtrees(backVersionedInterpolantsMap);
	}

	private TreeRun<TermRankedLetter, IPredicate> buildNestedFormulaTree(final TreeRun<HornClause, IPredicate> tree,
			int treeIdx, int childPos) {
		
		/*
		 * do the actual versioning
		 */
		final VariableVersioneer vvRoot = new VariableVersioneer(tree.getRootSymbol());
		mCurrentTree = getOrConstructIndex(tree);
		vvRoot.versionOutVars(childPos);
		mCurrentTree = treeIdx;
		vvRoot.versionOldVars(childPos);
		mSubsMap.put(tree, vvRoot);
		
		/*
		 * recursively descend into the tree run
		 */
		List<TreeRun<TermRankedLetter, IPredicate>> childTrees = new ArrayList<>();
		for (int i = 0; i < tree.getChildren().size(); i++) {
			TreeRun<HornClause, IPredicate> child = tree.getChildren().get(i);
			mCurrentTree = getOrConstructIndex(tree);
			if (child.getRootSymbol() != null) {
				childTrees.add(buildNestedFormulaTree(child, mCurrentTree, i));
			}
		}
		
		if (childTrees.isEmpty()) {
			childTrees = Collections.singletonList(new TreeRun<TermRankedLetter, IPredicate>(
					mPredicateUnifier.getTruePredicate()));
		}

		return new TreeRun<>(tree.getRoot(), new TermRankedLetter(vvRoot.getVersioneeredTerm(), childTrees.size()), 
				childTrees);
	}

	private HCSsa buildSSA() {
		mCurrentTree = 0;
		final VariableVersioneer vvPre = new VariableVersioneer(mPreCondition);
		vvPre.versionPredicate(mCurrentTree);

		final TreeRun<TermRankedLetter, IPredicate> tree = buildNestedFormulaTree((TreeRun<HornClause, IPredicate>) mTreeRun, 0, 0);
		mCurrentTree = 0;
		final VariableVersioneer vvPost = new VariableVersioneer(mPostCondition);
		vvPost.versionPredicate(mCurrentTree);

		return new HCSsa(tree, vvPre.getVersioneeredTerm(), vvPost.getVersioneeredTerm());
	}

	public Map<Term, HCOutVar> getConstants2BoogieVar() {
		return mConstants2HCOutVar;
	}


	class VariableVersioneer {
		private final HornClause mTF;
		private final Map<Term, Term> mSubstitutionMapping = new HashMap<>();
		private final Map<Term, HCOutVar> mBackSubstitutionMapping = new HashMap<>();

		private final Term mFormula;
		private final IPredicate mPred;

		public VariableVersioneer(final HornClause tf) {
			mTF = tf;
			mFormula = transferToCurrentScriptIfNecessary(tf.getTransformula().getFormula());
			mPred = null;
		}

		public VariableVersioneer(final IPredicate p) {
			mTF = null;
			mFormula = transferToCurrentScriptIfNecessary(p.getFormula());
			mPred = p;
		}

		/**
		 * Build constant bv_index that represents BoogieVar bv that obtains a new
		 * value at position index.
		 * @param predPos 
		 */
		private Term buildVersion(final HCInVar bv, final int index) {
			assert mIndexedVarRepresentative.get(bv) == null
					|| !mIndexedVarRepresentative.get(bv).containsKey(index) : "version was already constructed";
			final Sort sort = transferToCurrentScriptIfNecessary(bv.getTermVariable()).getSort();
			final Term constant = PredicateUtils.getIndexedConstant(bv.getGloballyUniqueId(), sort, index,
					mIndexedConstants, mScript.getScript());
			mIndexedVarRepresentative.put(bv, index, constant);
			return constant;
		}

		/**
		 * Set the current version of BoogieVariable bv to the constant b_index and
		 * return b_index.
		 */
		private Term setCurrentVarVersion(final HCInVar inVar, final int index) {
			final Term var = buildVersion(inVar, index);
			mCurrentHcInVarVersion.put(inVar, var);
			return var;
		}
		
		/**
		 * If we currently keep a versioned Term for bv, returns that;
		 *  otherwise returns a freshly versioned Term for bv.
		 * @param bv
		 * @return
		 */
		private Term getOrConstructCurrentVarVersion(final HCInVar bv) {
			Term result = mCurrentHcInVarVersion.get(bv);
			if (result == null) {
				// variable was not yet assigned in the calling context
				result = setCurrentVarVersion(bv, mCurrentTree);
			}
			return result;
		}

		/**
		 * We are going through the TreeRun from root to leaf. Thus the first versioning we do is to version the outVars
		 * of a HornClause according to the versions we got from the parent node.
		 * @param currentPos 
		 */
		public void versionOutVars(int currentPos) {
			for (final Entry<IProgramVar, TermVariable> en : mTF.getTransformula().getOutVars().entrySet()) {
				final HCOutVar hv = (HCOutVar) en.getKey();
				final TermVariable tv = transferToCurrentScriptIfNecessary(en.getValue());
				final HCInVar inVar = mTF.getHornClauseSymbolTable().getOrConstructHCInVar(currentPos, 
						hv.getArgumentPos(), hv.getSort());
				final Term versioneered = getOrConstructCurrentVarVersion(inVar);
				mConstants2HCOutVar.put(versioneered, hv);
				mSubstitutionMapping.put(tv, versioneered);
				mBackSubstitutionMapping.put(versioneered, hv);
			}
		}

		/**
		 * As we are going through the TreeRun from root to leaf, the second versioning step is to version all the vars
		 * that are used by the child, but are not seen by the parent. This is the analogue to the assigned vars when
		 *  we are going from start to end of a trace..
		 * @param currentPos
		 */
		public void versionOldVars(final int currentPos) {

			for (final Entry<IProgramVar, TermVariable> en : mTF.getTransformula().getInVars().entrySet()) {
				HCInVar hv = (HCInVar) en.getKey();
				final TermVariable tv = transferToCurrentScriptIfNecessary(en.getValue());
				final Term versioneered = setCurrentVarVersion(hv, mCurrentTree);

				mSubstitutionMapping.put(tv, versioneered);
				
				final HCOutVar outVar = mTF.getHornClauseSymbolTable().getOrConstructHCOutVar(hv.getArgumentPos(), 
						hv.getSort());
				mBackSubstitutionMapping.put(versioneered, outVar);
			}
			
			for (TermVariable aux : mTF.getTransformula().getAuxVars()) {
				assert false : "rename this, too, right?..";
			}
		}

		public void versionPredicate(int currentTree) {
			for (final IProgramVar bv : mPred.getVars()) {
				final HCOutVar hv = (HCOutVar) bv;
				final TermVariable tv = transferToCurrentScriptIfNecessary(hv.getTermVariable());
				final HCInVar inVar = mTF.getHornClauseSymbolTable().getOrConstructHCInVar(currentTree, 
						hv.getArgumentPos(), hv.getSort());
				final Term versioneered = getOrConstructCurrentVarVersion(inVar);
				mConstants2HCOutVar.put(versioneered, hv);
				mSubstitutionMapping.put(tv, versioneered);
				mBackSubstitutionMapping.put(versioneered, hv);
			}

		}

		public Term getVersioneeredTerm() {
			if (mFormula == null) {
				// TODO(mostafa): A hack for precondition and post condition,
				// should be removed.
				return null;
			}
			final Substitution subst = new Substitution(mScript, mSubstitutionMapping);
			final Term result = subst.transform(mFormula);
			assert result.getFreeVars().length == 0 : "free vars in versioneered term: "
					+ String.valueOf(result.getFreeVars());
			return result;
		}

		/**
		 * Reverts the SSA-renaming of the TermVariables that come from program variables in a
		 * term that comes from a (get-interpolants).
		 * 
		 * @param pl
		 * @param term
		 * @return
		 */
		public IPredicate backVersion(final Term term) {
			final Set<IProgramVar> vars = new HashSet<>();
			final Map<Term, Term> backSubstitutionMap = new HashMap<>();
			final Map<Term, HCOutVar> termToHcVar = new HashMap<>();
			for (Entry<Term, HCOutVar> en : mBackSubstitutionMapping.entrySet()) {
				vars.add(en.getValue());
				Term ssaTerm = transferToCurrentScriptIfNecessary(en.getKey());
				HCOutVar hcVarForSsaTerm = en.getValue();
				Term hcVarForSsaTermTermVariable = transferToCurrentScriptIfNecessary(
						hcVarForSsaTerm.getTermVariable());

				backSubstitutionMap.put(ssaTerm, hcVarForSsaTermTermVariable);
				termToHcVar.put(en.getValue().getTerm(), en.getValue());

			}

			final Substitution subst = new Substitution(mScript, backSubstitutionMap);
			final Term t = transferToCurrentScriptIfNecessary(term);
			final Term formula = subst.transform(t);
			
			final IPredicate unified = mPredicateUnifier.getOrConstructPredicate(formula);
			assert new HashSet<>(Arrays.asList(unified.getFormula().getFreeVars()))
				.equals(unified.getVars().stream().map(pv -> pv.getTermVariable()).collect(Collectors.toSet())) :
					"the free variables in the predicate must match the programvars";
			assert unified.getClosedFormula().getFreeVars().length == 0;
			return unified;
		}

		private TermVariable transferToCurrentScriptIfNecessary(final TermVariable tv) {
			final TermVariable result;
			if (mTransferToScriptNeeded) {
				result = (TermVariable) mTermTransferrer.transform(tv);
			} else {
				result = tv;
			}
			return result;
		}

		private Term transferToCurrentScriptIfNecessary(final Term term) {
			final Term result;
			if (mTransferToScriptNeeded) {
				result = mTermTransferrer.transform(term);
			} else {
				result = term;
			}
			return result;
		}

	}

}
