package de.uni_freiburg.informatik.ultimate.plugins.generator.treeautomizer.graph;

import de.uni_freiburg.informatik.ultimate.automata.tree.Tree;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;

public class HCSsa {
	private final Tree<Term> nestedFormulas;
	private final Term postCondition;
	private final Term preCondition;
	
	
	public HCSsa(final Tree<Term> t, final Term pre, final Term post) {
		nestedFormulas = t;
		postCondition = post;
		preCondition = pre;
	}
}
