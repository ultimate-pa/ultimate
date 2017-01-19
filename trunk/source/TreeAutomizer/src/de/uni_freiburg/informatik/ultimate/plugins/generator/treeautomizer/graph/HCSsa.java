package de.uni_freiburg.informatik.ultimate.plugins.generator.treeautomizer.graph;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.automata.tree.TreeRun;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;

/**HCSsa HornClause-SSA
 * */
public class HCSsa {
	private final TreeRun<Term, HCPredicate> mNestedFormulas;
	private final Term mPostCondition;
	private final Term mPreCondition;
	private final Map<Term, Integer> mCounters;
	private final Map<Term, Term> mTermToAssertion;
	
	public HCSsa(final TreeRun<Term, HCPredicate> t, final Term pre, final Term post, final Map<Term, Integer> counters) {
		mNestedFormulas = t;
		mPostCondition = post;
		mPreCondition = pre;
		mCounters = counters;
		mTermToAssertion = new HashMap<>();
	}
	
	public HCSsa(final HCSsa ssa, final TreeRun<Term, HCPredicate> nestedFormulas) {
		 mNestedFormulas = nestedFormulas;
		 mPostCondition = ssa.mPostCondition;
		 mPreCondition = ssa.mPreCondition;
		 mCounters = ssa.mCounters;
		 mTermToAssertion = ssa.mTermToAssertion;
	}
	
	protected int getCounter(final Term t) {
		if (!mCounters.containsKey(t)) {
			int r = mCounters.size() + 1;
			mCounters.put(t, r);
		}
		return mCounters.get(t);
	}
	
	protected String getName(final Term t) {
		return "HCsSATerm_" + getCounter(t);
	}
	
	/**
	 * @return return a flat version of the SSA.
	 * */
	public List<Term> flatten() {
		return flatten(mNestedFormulas);
	}
	
	private List<Term> flatten(final TreeRun<Term, HCPredicate> tree) {
		ArrayList<Term> res = new ArrayList<>();
		for (final TreeRun<Term, HCPredicate> child : tree.getChildren()) {
			res.addAll(flatten(child));
		}
		if (tree.getRootSymbol() != null) {
			//final Annotation ann = new Annotation(":named", getName(tree.getRootSymbol()));
			res.add(tree.getRootSymbol());
		}
		return res;
	}
	
	public TreeRun<Term, HCPredicate> getFormulasTree() {
		return mNestedFormulas;
	}

	protected Term getPredicateVariable(final Term term, final ManagedScript script) {
		script.lock(this);
		if (!mTermToAssertion.containsKey(term)) {
			final String name = getName(term);
			mTermToAssertion.put(term, script.term(this, name));
		}

		final Term result = mTermToAssertion.get(term);
		script.unlock(this);
		return result;
	}
}

