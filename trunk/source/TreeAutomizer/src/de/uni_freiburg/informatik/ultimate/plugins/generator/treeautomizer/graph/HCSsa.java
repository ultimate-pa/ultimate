package de.uni_freiburg.informatik.ultimate.plugins.generator.treeautomizer.graph;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.automata.tree.TreeRun;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;

/**HCSsa HornClause-SSA
 * */
public class HCSsa {
	private final TreeRun<Term, HCPredicate> nestedFormulas;
	private final Term postCondition;
	private final Term preCondition;
	private final Map<Term, Integer> mCounters;
	private final Map<Term, Term> mTermToAssertion;
	
	public HCSsa(final TreeRun<Term, HCPredicate> t, final Term pre, final Term post, final Map<Term, Integer> counters) {
		nestedFormulas = t;
		postCondition = post;
		preCondition = pre;
		mCounters = counters;
		mTermToAssertion = new HashMap<>();
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
		return flatten(nestedFormulas);
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
		return nestedFormulas;
	}

	protected Term getPredicateVariable(final Term term, final Script script) {
		if (!mTermToAssertion.containsKey(term)) {
			final String name = getName(term);
			mTermToAssertion.put(term, script.term(name));
		}

		return mTermToAssertion.get(term);
	}
}

