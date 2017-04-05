package de.uni_freiburg.informatik.ultimate.plugins.generator.treeautomizer.graph;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.automata.tree.ITreeRun;
import de.uni_freiburg.informatik.ultimate.automata.tree.TreeAutomatonRule;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hornutil.HornClause;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;

/**
 * Provides rules that might be added to an interpolant automaton during the generalization phase. 
 * 
 * 
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 */
public class CandidateRuleProvider {
	
	
	
	private Iterable<TreeAutomatonRule<HornClause, IPredicate>> mCandidateRules;

	/**
	 * Triggers computation of candidate rules.
	 * Result can be obtained via getter method.
	 * 
	 * @param originalTreeRun
	 * @param hcSymbolsToInterpolants 
	 * @param alphabet 
	 */
	public CandidateRuleProvider(ITreeRun<HornClause, IPredicate> originalTreeRun, 
			Map<IPredicate, IPredicate> hcSymbolsToInterpolants, List<HornClause> alphabet) {
		mCandidateRules = new ArrayList<>();
		
		for (HornClause letter : alphabet) {
			
			
		}

	}

	public Iterable<TreeAutomatonRule<HornClause, IPredicate>> getCandidateRules() {
		return mCandidateRules;
	}
}
