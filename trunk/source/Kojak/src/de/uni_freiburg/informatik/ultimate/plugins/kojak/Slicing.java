package de.uni_freiburg.informatik.ultimate.plugins.kojak;

import java.util.HashMap;
import java.util.HashSet;

import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ParallelComposition;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.SequentialComposition;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.StatementSequence;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.SmtManager;

public class Slicing {
	
	private SmtManager mSmtManager = null;
	private HashMap<CodeBlock, LBool> mCheckedTransitions =
			new HashMap<CodeBlock, LBool>();
	
	public Slicing(SmtManager smt_Manager) {
		mSmtManager = smt_Manager;
	}
	
	public void slice(HashSet<CodeBlock> slicableEdges) {
		for(CodeBlock cd: slicableEdges) {
			checkTransition(cd);
		}
	}
	
	public LBool checkTransition(CodeBlock transition) {
		LBool result = mCheckedTransitions.get(transition);
		if (result == null) {
			if (transition instanceof StatementSequence
					|| transition instanceof ParallelComposition
					|| transition instanceof SequentialComposition) {
				KojakProgramPoint sourcePP = (KojakProgramPoint)transition.getSource();
				KojakProgramPoint targetPP = (KojakProgramPoint)transition.getTarget();
				result = mSmtManager.isInductive(sourcePP.getPredicate(),
						transition, targetPP.getPredicate());
				mCheckedTransitions.put(transition, result);
			} else {
				result = LBool.SAT;
			}
		}
		return result;
	}
}
