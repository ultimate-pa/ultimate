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
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.tree.ITreeRun;
import de.uni_freiburg.informatik.ultimate.automata.tree.TreeRun;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.MultiElementCounter;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hornutil.HCVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hornutil.HornClause;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.Substitution;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.TermTransferrer;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.PredicateUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap2;

/**
 * SSABuilder
 * 
 * @author mostafa (mostafa.amin93@gmail.com) A class the is used for building
 *         an SSA from a given TreeRun.
 */
public class HCSSABuilder {

	private final ITreeRun<HornClause, HCPredicate> mTreeRun;
	private final HCPredicate mPostCondition;
	private final HCPredicate mPreCondition;
	private final ManagedScript mScript;

	private final HCSsa mResult;

	private final boolean mTransferToScriptNeeded;

	protected final Map<Term, HCVar> mConstants2HCVar = new HashMap<>();

	private final TermTransferrer mTermTransferrer;

	private final MultiElementCounter<TermVariable> mConstForTvCounter = new MultiElementCounter<>();

	private final Map<HCVar, Term> mCurrentLocalAndOldVarVersion;

//	private final Map<HCVar, TreeMap<Integer, Term>> mIndexedVarRepresentative = new HashMap<>();
	private final NestedMap2<HCVar, Integer, Term> mIndexedVarRepresentative = new NestedMap2<>();

	private final Map<TreeRun<HornClause, HCPredicate>, VariableVersioneer> mSubsMap;
	
	
	private final Map<Term, Integer> mCounters;
	private int mCurrentTree = -1;
	private final Map<String, Term> mIndexedConstants = new HashMap<>();

	private final HCPredicateFactory mPredicateFactory;

	public HCSSABuilder(final ITreeRun<HornClause, HCPredicate> trace, final HCPredicate preCondition,
			final HCPredicate postCondition, final ManagedScript script, final HCPredicateFactory predicateFactory) {
		mTreeRun = trace;
		mScript = script;
		mTermTransferrer = new TermTransferrer(mScript.getScript());
		mTransferToScriptNeeded = false;
		mPreCondition = preCondition;
		mPostCondition = postCondition;
		mCounters = new HashMap<>();
		mSubsMap = new HashMap<>();
		mPredicateFactory = predicateFactory;

		mCurrentLocalAndOldVarVersion = new HashMap<>();
		mResult = buildSSA();
	}

	public HCSSABuilder(final ITreeRun<HornClause, HCPredicate> trace, final ManagedScript script, 
			final HCPredicateFactory predicateFactory) {
		this(trace, null, null, script, predicateFactory);
	}

	public HCSsa getSSA() {
		return mResult;
	}

	private final Map<TreeRun<HornClause, HCPredicate>, Integer> idxMap = new HashMap<>();
	private int curIdx = 0;

	private int getIndex(final TreeRun<HornClause, HCPredicate> tree) {
		if (!idxMap.containsKey(tree)) {
			idxMap.put(tree, ++curIdx);
		}
		return idxMap.get(tree);
	}

	public Map<HCPredicate, HCPredicate> rebuildSSApredicates(final Map<HCPredicate, Term> interpolantsMap) {
		final Map<HCPredicate, HCPredicate> res = new HashMap<>();
		mCurrentTree = 0;
		rebuild((TreeRun<HornClause, HCPredicate>) mTreeRun, res, interpolantsMap);
		return res;
	}
	
	private void rebuild(final TreeRun<HornClause, HCPredicate> tree, final Map<HCPredicate, HCPredicate> res,
			final Map<HCPredicate, Term> interpolantsMap) {
		for (final TreeRun<HornClause, HCPredicate> child : tree.getChildren()) {
			mCurrentTree = getIndex(tree);
			rebuild(child, res, interpolantsMap);
		}

		if (tree.getRootSymbol() == null) {
			//tree.getRoot(); // TODO;
			res.put(tree.getRoot(), tree.getRoot());
			return ;
		}
		mCurrentTree = getIndex(tree);
		final VariableVersioneer vvRoot = mSubsMap.get(tree);
		if (interpolantsMap.containsKey(tree.getRoot())) {
			res.put(tree.getRoot(), vvRoot.backVersion(tree.getRoot(), interpolantsMap.get(tree.getRoot())));
		} else {
			res.put(tree.getRoot(), tree.getRoot());
		}
	}


	private TreeRun<Term, HCPredicate> buildNestedFormulaTree(final TreeRun<HornClause, HCPredicate> tree, int treeIdx) {
		final ArrayList<TreeRun<Term, HCPredicate>> childTrees = new ArrayList<>();
		//int treeBk = currentTree;
		for (final TreeRun<HornClause, HCPredicate> child : tree.getChildren()) {
			mCurrentTree = getIndex(tree);
			childTrees.add(buildNestedFormulaTree(child, mCurrentTree));
		}

		if (tree.getRootSymbol() == null) {
			return new TreeRun<>(tree.getRoot(), null, childTrees);
		}
		final VariableVersioneer vvRoot = new VariableVersioneer(tree.getRootSymbol());
		mCurrentTree = getIndex(tree);
		vvRoot.versionInVars();
		mCurrentTree = treeIdx;
		vvRoot.versionAssignedVars(mCurrentTree);
		mSubsMap.put(tree, vvRoot);
		//currentTree = treeBk;

		return new TreeRun<>(tree.getRoot(), vvRoot.getVersioneeredTerm(), childTrees);
	}

	private HCSsa buildSSA() {
		mCurrentTree = 0;
		final VariableVersioneer vvPre = new VariableVersioneer(mPreCondition);
		vvPre.versionPredicate();

		final TreeRun<Term, HCPredicate> tree = buildNestedFormulaTree((TreeRun<HornClause, HCPredicate>) mTreeRun, 0);
		mCurrentTree = 0;
		final VariableVersioneer vvPost = new VariableVersioneer(mPostCondition);
		vvPost.versionPredicate();

		return new HCSsa(tree, vvPre.getVersioneeredTerm(), vvPost.getVersioneeredTerm(), mCounters);
	}

	public Map<Term, HCVar> getConstants2BoogieVar() {
		return mConstants2HCVar;
	}

	private Term getCurrentVarVersion(final HCVar bv) {
		Term result = mCurrentLocalAndOldVarVersion.get(bv);
		 if (result == null) {
			 // variable was not yet assigned in the calling context
			 result = setCurrentVarVersion(bv, mCurrentTree);
		}
		return result;
	}

	/**
	 * Set the current version of BoogieVariable bv to the constant b_index and
	 * return b_index.
	 */
	private Term setCurrentVarVersion(final HCVar bv, final int index) {
		final Term var = buildVersion(bv, index);
		if (mCurrentLocalAndOldVarVersion.containsKey(bv)) {
			mCurrentLocalAndOldVarVersion.remove(bv);
		}
		mCurrentLocalAndOldVarVersion.put(bv, var);

		return var;
	}

	/**
	 * Build constant bv_index that represents BoogieVar bv that obtains a new
	 * value at position index.
	 */
	private Term buildVersion(final HCVar bv, final int index) {
//		TreeMap<Integer, Term> index2constant = mIndexedVarRepresentative.get(bv);
//		if (index2constant == null) {
//			index2constant = new TreeMap<>();
//			mIndexedVarRepresentative.put(bv, index2constant);
//		}
//		assert !index2constant.containsKey(index) : "version was already constructed";
		assert mIndexedVarRepresentative.get(bv) == null || !mIndexedVarRepresentative.get(bv).containsKey(index) : 
			"version was already constructed";
		final Sort sort = transferToCurrentScriptIfNecessary(bv.getTermVariable()).getSort();
		final Term constant = PredicateUtils.getIndexedConstant(bv.getGloballyUniqueId(), sort, index,
				mIndexedConstants, mScript.getScript());
//		index2constant.put(index, constant);
		mIndexedVarRepresentative.put(bv, index, constant);
		return constant;
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

	class VariableVersioneer {
		private final HornClause mTF;
		private final Map<Term, Term> mSubstitutionMapping = new HashMap<>();
		private final Map<Term, HCVar> mBackSubstitutionMapping = new HashMap<>();
		private final Term mformula;
		private final HCPredicate mPred;

		public VariableVersioneer(final HornClause tf) {
			mTF = tf;
			mformula = transferToCurrentScriptIfNecessary(tf.getTransformula().getFormula());
			mPred = null;
		}

		public VariableVersioneer(final HCPredicate p) {
			mTF = null;
			mformula = transferToCurrentScriptIfNecessary(p.getFormula());
			mPred = p;
		}

		public void versionInVars() {
			for (final IProgramVar bv : mTF.getTransformula().getInVars().keySet()) {
				HCVar hv = (HCVar) bv;
				final TermVariable tv = transferToCurrentScriptIfNecessary(mTF.getTransformula().getInVars().get(hv));
				final Term versioneered = getCurrentVarVersion(hv);
				mConstants2HCVar.put(versioneered, hv);
				mSubstitutionMapping.put(tv, versioneered);
				//mBackSubstitutionMapping.put(versioneered, bv);
			}
		}

		public void versionAssignedVars(final int currentPos) {

			for (final IProgramVar bv : mTF.getTransformula().getInVars().keySet()) {
				HCVar hv = (HCVar) bv;
				//final TermVariable tv = transferToCurrentScriptIfNecessary(mTF.getInVars().get(bv));
				final Term versioneered = getCurrentVarVersion(hv);
				//mConstants2HCVar.put(versioneered, bv);
				//mSubstitutionMapping.put(tv, versioneered);
				mBackSubstitutionMapping.put(versioneered, hv);
			}
			
			for (final IProgramVar bv : mTF.getTransformula().getOutVars().keySet()) {
				HCVar hv = (HCVar) bv;
				final TermVariable tv = transferToCurrentScriptIfNecessary(mTF.getTransformula().getOutVars().get(hv));
				final Term versioneered = setCurrentVarVersion(hv, currentPos);
				mConstants2HCVar.put(versioneered, hv);
				mSubstitutionMapping.put(tv, versioneered);
				mBackSubstitutionMapping.put(versioneered, hv);
			}
		}

		private Term constructFreshConstant(final TermVariable tv) {
			mScript.lock(this);
			final Integer newIndex = mConstForTvCounter.increase(tv);
			final String name = SmtUtils.removeSmtQuoteCharacters(tv.getName()) + "_fresh_" + newIndex;
			final Sort resultSort = tv.getSort();
			mScript.declareFun(this, name, new Sort[0], resultSort);
			final Term result = mScript.term(this, name);
			mScript.unlock(this);
			return result;
		}

		public void versionPredicate() {
			for (final IProgramVar bv : mPred.getVars()) {
				final HCVar hv = (HCVar) bv;
				final TermVariable tv = transferToCurrentScriptIfNecessary(hv.getTermVariable());
				final Term versioneered = getCurrentVarVersion(hv);
				mConstants2HCVar.put(versioneered, hv);
				mSubstitutionMapping.put(tv, versioneered);
				mBackSubstitutionMapping.put(versioneered, hv);
			}

		}

		public Term getVersioneeredTerm() {
			if (mformula == null) {
				// TODO(mostafa): A hack for precondition and post condition,
				// should be removed.
				return null;
			}
			final Substitution subst = new Substitution(mScript, mSubstitutionMapping);
			final Term result = subst.transform(mformula);
			assert result.getFreeVars().length == 0 : "free vars in versioneered term: "
					+ String.valueOf(result.getFreeVars());
			return result;
		}

		public HCPredicate backVersion(final HCPredicate pl, final Term term) {
//			final Map<Term, Term> backSubstitutionMap = new HashMap<>();
//			final Set<IProgramVar> vars = new HashSet<>();
//			final Map<Term, HCVar> substit = new HashMap<>();
//			for (final Term hcvar : mSubstitutionMapping.keySet()) {
//				backSubstitutionMap.put(mSubstitutionMapping.get(hcvar), hcvar);
//				if (mBackSubstitutionMapping.containsKey(mSubstitutionMapping.get(hcvar))) {
//					vars.add(mBackSubstitutionMapping.get(mSubstitutionMapping.get(hcvar)));
//					substit.put(hcvar, mBackSubstitutionMapping.get(mSubstitutionMapping.get(hcvar)));
//				}
//			}
			final Set<IProgramVar> vars = new HashSet<>();
			final Map<Term, Term> backSubstitutionMap = new HashMap<>();
			final Map<Term, HCVar> termToHcVar = new HashMap<>();
			for (Entry<Term, HCVar> en : mBackSubstitutionMapping.entrySet()) {
				vars.add(en.getValue());
				Term ssaTerm = transferToCurrentScriptIfNecessary(en.getKey());
				HCVar hcVarForSsaTerm = en.getValue();
				Term hcVarForSsaTermTermVariable = transferToCurrentScriptIfNecessary(hcVarForSsaTerm.getTermVariable());

				backSubstitutionMap.put(ssaTerm, hcVarForSsaTermTermVariable);
				termToHcVar.put(en.getValue().getTerm(), en.getValue());

			}
			
			
			final Substitution subst = new Substitution(mScript, backSubstitutionMap);
			final Term t = transferToCurrentScriptIfNecessary(term);
			final Term formula = subst.transform(t);
			
			return mPredicateFactory.newPredicate(pl.mProgramPoint, pl.hashCode(), formula, vars, termToHcVar);
		}
		
		public Map<Term, Term> getSubstitutionMapping() {
			return mSubstitutionMapping;
		}

	}

}
