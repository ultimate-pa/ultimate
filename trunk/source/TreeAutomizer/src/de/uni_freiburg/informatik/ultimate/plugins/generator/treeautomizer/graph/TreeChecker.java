package de.uni_freiburg.informatik.ultimate.plugins.generator.treeautomizer.graph;

import java.util.HashSet;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.automata.tree.ITreeRun;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hornutil.HornClause;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;

public class TreeChecker {
	
	private final ITreeRun<HornClause, HCPredicate> mTree;
	private final ManagedScript mBackendSmtSolverScript;
	private final HCPredicate mPostCondition;
	private final HCPredicate mPreCondition;
	private final HCSSABuilder mSSABuilder;
	private ILogger mLogger;
	
	public TreeChecker(final ITreeRun<HornClause, HCPredicate> tree,
			final ManagedScript backendSmtSolverScript, final HCPredicate preCondition,
			final HCPredicate postCondition, ILogger logger) {
		mTree = tree;
		mBackendSmtSolverScript = backendSmtSolverScript;
		mPostCondition = postCondition;
		mPreCondition = preCondition;
		mSSABuilder = new HCSSABuilder(mTree, mPreCondition, mPostCondition, mBackendSmtSolverScript);
		
		mLogger = logger;
	}
	
	public Map<HCPredicate, HCPredicate> rebuild(final Map<HCPredicate, Term> interpolantsMap) {
		return mSSABuilder.rebuildSSApredicates(interpolantsMap);
	}
	
	protected HCSsa getSSA() {
		return mSSABuilder.getSSA();
	}

	protected LBool checkTrace() {
		mBackendSmtSolverScript.lock(this);
		final HCSsa ssa = getSSA();
		final List<Term> nestedExp = ssa.flatten();
		HashSet<Integer> visited = new HashSet<>();
		for (final Term t : nestedExp) {
			final Annotation ann = new Annotation(":named", ssa.getName(t));
			if (!visited.contains(ssa.getCounter(t))) {
				mLogger.debug("assert: " + ssa.getName(t) + " :: " + t.toString());
				visited.add(ssa.getCounter(t));
				//mBackendSmtSolverScript.term(annT, {});
				final Term annT = mBackendSmtSolverScript.annotate(this, t, ann);
				mBackendSmtSolverScript.assertTerm(this, annT);
			}
		}
		final LBool result = mBackendSmtSolverScript.checkSat(this);
		mBackendSmtSolverScript.unlock(this);
		return result;
	}

}
