package de.uni_freiburg.informatik.ultimate.plugins.generator.treeautomizer.graph;

import java.util.HashSet;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.automata.tree.ITreeRun;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hornutil.HCTransFormula;

public class TreeChecker {
	
	private final ITreeRun<HCTransFormula, HCPredicate> mTree;
	private final Script mBackendSmtSolverScript;
	private final HCPredicate mPostCondition;
	private final HCPredicate mPreCondition;
	private final SSABuilder mSSABuilder;
	private ILogger mLogger;
	
	public TreeChecker(final ITreeRun<HCTransFormula, HCPredicate> tree,
			final Script backendSmtSolverScript, final HCPredicate preCondition,
			final HCPredicate postCondition, ILogger logger) {
		mTree = tree;
		mBackendSmtSolverScript = backendSmtSolverScript;
		mPostCondition = postCondition;
		mPreCondition = preCondition;
		mSSABuilder = new SSABuilder(mTree, mPreCondition, mPostCondition, mBackendSmtSolverScript);
		
		mLogger = logger;
	}
	
	
	protected HCSsa getSSA() {
		return mSSABuilder.getSSA();
	}

	protected LBool checkTrace() {
		final HCSsa ssa = getSSA();
		final List<Term> nestedExp = ssa.flatten();
		HashSet<Integer> visited = new HashSet<>();
		for (final Term t : nestedExp) {
			final Annotation ann = new Annotation(":named", ssa.getName(t));
			if (!visited.contains(ssa.getCounter(t))) {
				mLogger.debug("assert: " + ssa.getName(t) + " :: " + t.toString());
				visited.add(ssa.getCounter(t));
				//mBackendSmtSolverScript.term(annT, {});
				final Term annT = mBackendSmtSolverScript.annotate(t, ann);
				mBackendSmtSolverScript.assertTerm(annT);
			}
		}
		return mBackendSmtSolverScript.checkSat();
	}

}
