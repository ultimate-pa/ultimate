package de.uni_freiburg.informatik.ultimate.plugins.generator.treeautomizer.graph;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;

import de.uni_freiburg.informatik.ultimate.automata.tree.ITreeRun;
import de.uni_freiburg.informatik.ultimate.automata.tree.TreeRun;
import de.uni_freiburg.informatik.ultimate.core.coreplugin.toolchain.BasicToolchainJob;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.MultiElementCounter;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hornutil.HCTransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hornutil.HCVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.Substitution;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.TermTransferrer;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.PredicateUtils;

/**
 * SSABuilder
 * 
 * @author mostafa (mostafa.amin93@gmail.com) A class the is used for building
 *         an SSA from a given TreeRun.
 */
public class SSABuilder {

	private final ITreeRun<HCTransFormula, HCPredicate> mTreeRun;
	private final HCPredicate mPostCondition;
	private final HCPredicate mPreCondition;
	private final Script mScript;

	private final HCSsa mResult;

	private final boolean mTransferToScriptNeeded;

	protected final Map<Term, HCVar> mConstants2HCVar = new HashMap<>();

	private final TermTransferrer mTermTransferrer;

	private final MultiElementCounter<TermVariable> mConstForTvCounter = new MultiElementCounter<>();

	private final Map<HCVar, Term> currentLocalAndOldVarVersion;

	private final Map<HCVar, TreeMap<Integer, Term>> mIndexedVarRepresentative = new HashMap<>();

	private final Map<TreeRun<HCTransFormula, HCPredicate>, VariableVersioneer> mSubsMap;
	
	
	private final Map<Term, Integer> mCounters;
	private int currentTree = -1;
	private final Map<String, Term> mIndexedConstants = new HashMap<>();

	public SSABuilder(final ITreeRun<HCTransFormula, HCPredicate> trace, final HCPredicate preCondition,
			final HCPredicate postCondition, final Script script) {
		mTreeRun = trace;
		mScript = script;
		mTermTransferrer = new TermTransferrer(mScript);
		mTransferToScriptNeeded = true;
		mPreCondition = preCondition;
		mPostCondition = postCondition;
		mCounters = new HashMap<>();
		mSubsMap = new HashMap<>();

		currentLocalAndOldVarVersion = new HashMap<>();
		mResult = buildSSA();
	}

	public SSABuilder(final ITreeRun<HCTransFormula, HCPredicate> trace, final Script script) {
		this(trace, null, null, script);
	}

	public HCSsa getSSA() {
		return mResult;
	}

	private final Map<TreeRun<HCTransFormula, HCPredicate>, Integer> idxMap = new HashMap<>();
	private int curIdx = 0;

	private int getIndex(final TreeRun<HCTransFormula, HCPredicate> tree) {
		if (!idxMap.containsKey(tree)) {
			idxMap.put(tree, ++curIdx);
		}
		return idxMap.get(tree);
	}

	public Map<HCPredicate, HCPredicate> rebuildSSApredicates(final Map<HCPredicate, Term> interpolantsMap) {
		final Map<HCPredicate, HCPredicate> res = new HashMap<>();
		rebuild((TreeRun<HCTransFormula, HCPredicate>) mTreeRun, res, interpolantsMap);
		return res;
	}
	
	private void rebuild(final TreeRun<HCTransFormula, HCPredicate> tree, final Map<HCPredicate, HCPredicate> res,
			final Map<HCPredicate, Term> interpolantsMap) {
		currentTree = getIndex(tree);
		for (final TreeRun<HCTransFormula, HCPredicate> child : tree.getChildren()) {
			rebuild(child, res, interpolantsMap);
		}

		if (tree.getRootSymbol() == null) {
			tree.getRoot(); // TODO;
			res.put(tree.getRoot(), tree.getRoot());
			return ;
		}
		final VariableVersioneer vvRoot = mSubsMap.get(tree);
		currentTree = getIndex(tree);
		if (interpolantsMap.containsKey(tree.getRoot())) {
			res.put(tree.getRoot(), vvRoot.backVersion(tree.getRoot(), interpolantsMap.get(tree.getRoot())));
		} else {
			res.put(tree.getRoot(), tree.getRoot());
		}
	}


	private TreeRun<Term, HCPredicate> buildNestedFormulaTree(final TreeRun<HCTransFormula, HCPredicate> tree) {
		final ArrayList<TreeRun<Term, HCPredicate>> childTrees = new ArrayList<>();
		currentTree = getIndex(tree);
		for (final TreeRun<HCTransFormula, HCPredicate> child : tree.getChildren()) {
			childTrees.add(buildNestedFormulaTree(child));
		}

		if (tree.getRootSymbol() == null) {
			return new TreeRun<>(tree.getRoot(), null, childTrees);
		}
		final VariableVersioneer vvRoot = new VariableVersioneer(tree.getRootSymbol());
		vvRoot.versionInVars();
		currentTree = getIndex(tree);
		vvRoot.versionAssignedVars(currentTree);
		
		mSubsMap.put(tree, vvRoot);

		return new TreeRun<>(tree.getRoot(), vvRoot.getVersioneeredTerm(), childTrees);
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
		// if (result == null) {
		// variable was not yet assigned in the calling context
		result = setCurrentVarVersion(bv, currentTree);
		// }
		return result;
	}

	/**
	 * Set the current version of BoogieVariable bv to the constant b_index and
	 * return b_index.
	 */
	private Term setCurrentVarVersion(final HCVar bv, final int index) {
		final Term var = buildVersion(bv, index);
		if (currentLocalAndOldVarVersion.containsKey(bv)) {
			currentLocalAndOldVarVersion.remove(bv);
		}
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
			index2constant = new TreeMap<>();
			mIndexedVarRepresentative.put(bv, index2constant);
		}
		assert !index2constant.containsKey(index) : "version was already constructed";
		final Sort sort = transferToCurrentScriptIfNecessary(bv.getTermVariable()).getSort();
		final Term constant = PredicateUtils.getIndexedConstant(bv.getGloballyUniqueId(), sort, index,
				mIndexedConstants, mScript);
		index2constant.put(index, constant);
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
			for (final IProgramVar bv : mPred.getVars()) {
				final HCVar hv = (HCVar) bv;
				final TermVariable tv = transferToCurrentScriptIfNecessary(hv.getTermVariable());
				final Term versioneered = getCurrentVarVersion(hv);
				mConstants2HCVar.put(versioneered, hv);
				mSubstitutionMapping.put(tv, versioneered);
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
			final Map<Term, Term> backSubstitutionMap = new HashMap<>();
			final Set<IProgramVar> vars = new HashSet<>();
			for (final Term hcvar : mSubstitutionMapping.keySet()) {
				backSubstitutionMap.put(mSubstitutionMapping.get(hcvar), hcvar);
				vars.add(mConstants2HCVar.get(mSubstitutionMapping.get(hcvar)));
			}
			
			final Substitution subst = new Substitution(mScript, backSubstitutionMap);
			final Term t = transferToCurrentScriptIfNecessary(term);
			final Term formula = subst.transform(t);
			
			return new HCPredicate(pl.mProgramPoint, pl.hashCode(), formula, vars);
		}
		
		public Map<Term, Term> getSubstitutionMapping() {
			return mSubstitutionMapping;
		}

	}

}
