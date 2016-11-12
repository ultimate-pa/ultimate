package de.uni_freiburg.informatik.ultimate.plugins.generator.treeautomizer.graph;

import java.util.HashSet;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.automata.tree.ITreeRun;
import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hornutil.HCTransFormula;

public class TreeChecker {
	
	private final ITreeRun<HCTransFormula, HCPredicate> mTree;
	private final Script mBackendSmtSolverScript;
	private final Map<Term, Integer> mCounters;
	private final HCPredicate mPostCondition, mPreCondition;
	private final SSABuilder mSSABuilder;
	
	public TreeChecker(final ITreeRun<HCTransFormula, HCPredicate> tree,
			final Script backendSmtSolverScript,
			final Map<Term, Integer> counters,
			final HCPredicate preCondition, final HCPredicate postCondition) {
		mTree = tree;
		mBackendSmtSolverScript = backendSmtSolverScript;
		mCounters = counters;
		mPostCondition = postCondition;
		mPreCondition = preCondition;
		mSSABuilder = new SSABuilder(mTree, mBackendSmtSolverScript, mPreCondition, mPostCondition, mCounters);
	}
	
	
	protected HCSsa getSSA() {
		return mSSABuilder.getSSA();
	}

	protected LBool checkTrace() {
		final HCSsa ssa = getSSA();
		final List<Term> nestedExp = ssa.flatten();
		// TODO(mostafa): Check if 'visited' needs to be removed.
		HashSet<Integer> visited = new HashSet<>();
		for (final Term t : nestedExp) {
			final Annotation ann = new Annotation(":named", ssa.getName(t));
			if (!visited.contains(ssa.getCounter(t))) {
				System.err.println("assert: " + ssa.getName(t) + t.toString());
				visited.add(ssa.getCounter(t));
				//mBackendSmtSolverScript.term(annT, {});
				final Term annT = mBackendSmtSolverScript.annotate(t, ann);
				mBackendSmtSolverScript.assertTerm(annT);
			}
		}
		return mBackendSmtSolverScript.checkSat();
	}

}
