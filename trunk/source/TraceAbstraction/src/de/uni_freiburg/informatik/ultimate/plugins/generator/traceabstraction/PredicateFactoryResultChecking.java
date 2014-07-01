package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction;

import java.util.Collection;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.buchiNwa.BuchiComplementFKVNwa.LevelRankingState;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;

/**
 * StateFactory that should be used for result checking. 
 * Supports most operations but constructs always only an auxiliary predicate.
 * @author Matthias Heizmann
 *
 */
public class PredicateFactoryResultChecking extends StateFactory<IPredicate> {
	
	protected final SmtManager m_SmtManager;
	private final String s_StateLabel = 
			"auxiliary predicate that should only be used while checking correctness of automata operations";
	
	public PredicateFactoryResultChecking(SmtManager smtManager) {
		m_SmtManager = smtManager;
	}

	
	public IPredicate intersection(IPredicate p1, IPredicate p2) {
		return m_SmtManager.newDebugPredicate(s_StateLabel);
	}
	


	@Override
	public IPredicate determinize(Map<IPredicate, Set<IPredicate>> down2up) {
		return m_SmtManager.newDebugPredicate(s_StateLabel);
	}

	
	public IPredicate createSinkStateContent() {
		return m_SmtManager.newDebugPredicate(s_StateLabel);
	}

	
	@Override
	public IPredicate createEmptyStackState(){
		return m_SmtManager.newDebugPredicate(s_StateLabel);
	}


	@Override
	public IPredicate createDoubleDeckerContent(IPredicate down,
			IPredicate up) {
		throw new UnsupportedOperationException();
	}

	
	@Override
	public IPredicate minimize(Collection<IPredicate> states) {
		return m_SmtManager.newDebugPredicate(s_StateLabel);
	}
	
	@Override
	public IPredicate senwa(IPredicate entry, IPredicate state) {
		assert false : "still used?";
		return m_SmtManager.newDontCarePredicate(((SPredicate) state).getProgramPoint());
	}


	@Override
	public IPredicate buchiComplementFKV(LevelRankingState compl) {
		return m_SmtManager.newDebugPredicate(s_StateLabel);
	}


	@Override
	public IPredicate intersectBuchi(IPredicate s1, IPredicate s2, int track) {
		return m_SmtManager.newDebugPredicate(s_StateLabel);
	}
	
	@Override
	public IPredicate getContentOnConcurrentProduct(IPredicate c1,
			IPredicate c2) {
		return m_SmtManager.newDebugPredicate(s_StateLabel);
	}
	
	
}
