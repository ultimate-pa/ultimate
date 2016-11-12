package de.uni_freiburg.informatik.ultimate.plugins.generator.treeautomizer.graph;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.Map;
import java.util.TreeMap;

import de.uni_freiburg.informatik.ultimate.automata.tree.ITreeRun;
import de.uni_freiburg.informatik.ultimate.automata.tree.Tree;
import de.uni_freiburg.informatik.ultimate.automata.tree.TreeRun;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.MultiElementCounter;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hornutil.HCTransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hornutil.HCVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.Substitution;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.TermTransferrer;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.PredicateUtils;

public class SSABuilder {
	private final ITreeRun<HCTransFormula, HCPredicate> mTreeRun;
	private final HCPredicate mPostCondition;
	private final HCPredicate mPreCondition;
	private final Script mScript;

	private final HCSsa mResult;

	private final boolean mTransferToScriptNeeded;

	protected final Map<Term, HCVar> mConstants2HCVar = new HashMap<>();

	private final TermTransferrer mTermTransferrer;

	private final MultiElementCounter<TermVariable> mConstForTvCounter = new MultiElementCounter<TermVariable>();

	private final Map<HCVar, Term> currentLocalAndOldVarVersion;

	private final Map<HCVar, TreeMap<Integer, Term>> mIndexedVarRepresentative = new HashMap<HCVar, TreeMap<Integer, Term>>();

	private final Map<Term, Integer> mCounters;
	private int currentTree = -1;
	private final Map<String, Term> mIndexedConstants = new HashMap<String, Term>();

	public SSABuilder(final ITreeRun<HCTransFormula, HCPredicate> trace, final Script script,
			final HCPredicate preCondition, final HCPredicate postCondition, 
			final Map<Term, Integer> counters) {
		mTreeRun = trace;
		mScript = script;
		mTermTransferrer = new TermTransferrer(mScript);
		mTransferToScriptNeeded = true;
		mPreCondition = preCondition;
		mPostCondition = postCondition;
		mCounters = counters;

		currentLocalAndOldVarVersion = new HashMap<>();
		mResult = buildSSA();
	}

	public SSABuilder(final ITreeRun<HCTransFormula, HCPredicate> trace, final Script script) {
		this(trace, script, null, null, new HashMap<>());
	}

	public HCSsa getSSA() {
		return mResult;
	}

	private final Map<TreeRun<HCTransFormula, HCPredicate>, Integer> idxMap = new HashMap<>();
	private int curIdx = 0;

	public int getIndex(final TreeRun<HCTransFormula, HCPredicate> tree) {
		if (!idxMap.containsKey(tree)) {
			idxMap.put(tree, ++curIdx);
		}
		return idxMap.get(tree);
	}

	private TreeRun<Term, HCPredicate> buildNestedFormulaTree(final TreeRun<HCTransFormula, HCPredicate> tree) {
		final ArrayList<TreeRun<Term, HCPredicate>> childTrees = new ArrayList<>();
		currentTree = getIndex(tree);
		for (final TreeRun<HCTransFormula, HCPredicate> child : tree.getChildren()) {
			childTrees.add(buildNestedFormulaTree(child));
		}

		if (tree.getRootSymbol() == null) {
			return new TreeRun<Term, HCPredicate>(tree.getRoot(), null, childTrees);
		}
		final VariableVersioneer vvRoot = new VariableVersioneer(tree.getRootSymbol());
		vvRoot.versionInVars();
		vvRoot.versionAssignedVars(getIndex(tree));
		
		currentTree = getIndex(tree);

		return new TreeRun<Term, HCPredicate>(tree.getRoot(), vvRoot.getVersioneeredTerm(), childTrees);
	}

	private HCSsa buildSSA() {
		currentTree = 0;
		final VariableVersioneer vvPre = new VariableVersioneer(mPreCondition);
		vvPre.versionPredicate();

		final TreeRun<Term, HCPredicate> tree = buildNestedFormulaTree((TreeRun<HCTransFormula, HCPredicate>) mTreeRun);
		currentTree = 0;
		final VariableVersioneer vvPost = new VariableVersioneer(mPostCondition);
		vvPost.versionPredicate();

		return new HCSsa(tree, vvPre.getVersioneeredTerm(), vvPost.getVersioneeredTerm(), mCounters);
	}

	public Map<Term, HCVar> getConstants2BoogieVar() {
		return mConstants2HCVar;
	}

	private Term getCurrentVarVersion(final HCVar bv) {
		Term result = currentLocalAndOldVarVersion.get(bv);
		if (result == null) {
			// variable was not yet assigned in the calling context
			result = setCurrentVarVersion(bv, currentTree);
		}

		return result;
	}

	/**
	 * Set the current version of BoogieVariable bv to the constant b_index and
	 * return b_index.
	 */
	private Term setCurrentVarVersion(final HCVar bv, final int index) {
		final Term var = buildVersion(bv, index);

		currentLocalAndOldVarVersion.put(bv, var);

		return var;
	}

	/**
	 * Build constant bv_index that represents BoogieVar bv that obtains a new
	 * value at position index.
	 */
	private Term buildVersion(final HCVar bv, final int index) {
		TreeMap<Integer, Term> index2constant = mIndexedVarRepresentative.get(bv);
		if (index2constant == null) {
			index2constant = new TreeMap<Integer, Term>();
			mIndexedVarRepresentative.put(bv, index2constant);
		}
		assert !index2constant.containsKey(index) : "version was already constructed";
		final Sort sort = transferToCurrentScriptIfNecessary(bv.getTermVariable()).getSort();
		final Term constant = PredicateUtils.getIndexedConstant(bv.getGloballyUniqueId(), sort, index,
				mIndexedConstants, mScript);
		index2constant.put(index, constant);
		return constant;
	}

	// TODO
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
		private final HCTransFormula mTF;
		private final Map<Term, Term> mSubstitutionMapping = new HashMap<>();
		private final Term mformula;
		private final HCPredicate mPred;

		public VariableVersioneer(final HCTransFormula tf) {
			mTF = tf;
			mformula = transferToCurrentScriptIfNecessary(tf.getFormula());
			mPred = null;
		}

		public VariableVersioneer(final HCPredicate p) {
			mTF = null;
			mformula = transferToCurrentScriptIfNecessary(p.getFormula());
			mPred = p;
		}

		public void versionInVars() {
			for (final HCVar bv : mTF.getInVars().keySet()) {
				final TermVariable tv = transferToCurrentScriptIfNecessary(mTF.getInVars().get(bv));
				final Term versioneered = getCurrentVarVersion(bv);
				mConstants2HCVar.put(versioneered, bv);
				mSubstitutionMapping.put(tv, versioneered);
			}
		}

		public void versionAssignedVars(final int currentPos) {
			for (final HCVar bv : mTF.getOutVars().keySet()) {
				final TermVariable tv = transferToCurrentScriptIfNecessary(mTF.getOutVars().get(bv));
				final Term versioneered = setCurrentVarVersion(bv, currentPos);
				mConstants2HCVar.put(versioneered, bv);
				mSubstitutionMapping.put(tv, versioneered);
			}
		}

		private Term constructFreshConstant(final TermVariable tv) {
			final Integer newIndex = mConstForTvCounter.increase(tv);
			final String name = SmtUtils.removeSmtQuoteCharacters(tv.getName()) + "_fresh_" + newIndex;
			final Sort resultSort = tv.getSort();
			mScript.declareFun(name, new Sort[0], resultSort);
			return mScript.term(name);
		}

		public void versionPredicate() {
			/*
			 * for (final IProgramVar bv : mPred.getVars()) { final TermVariable
			 * tv = transferToCurrentScriptIfNecessary(bv.getTermVariable());
			 * final Term versioneered = getCurrentVarVersion(bv);
			 * mConstants2BoogieVar.put(versioneered, bv);
			 * mSubstitutionMapping.put(tv, versioneered); }
			 */
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

		public Map<Term, Term> getSubstitutionMapping() {
			return mSubstitutionMapping;
		}

	}

}
