package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.buchiNwa.BuchiComplementFKVNwa.LevelRankingState;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.preferences.TAPreferences.Determinization;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager.TermVarsProc;

public class PredicateFactory extends StateFactory<IPredicate> {
	
	final protected TAPreferences m_Pref;
	private final IPredicate m_emtpyStack; 
	protected final SmtManager m_SmtManager;
	
	
	public PredicateFactory(SmtManager smtManager,
							TAPreferences taPrefs) {
		m_Pref = taPrefs;
		m_SmtManager = smtManager;
		m_emtpyStack = m_SmtManager.newEmptyStackPredicate();
		
	}

	
	public IPredicate intersection(IPredicate p1, IPredicate p2) {
		TermVarsProc tvp = m_SmtManager.and(p1, p2);
		IPredicate result = m_SmtManager.newPredicate(tvp.getFormula(), 
				tvp.getProcedures(), tvp.getVars(), tvp.getClosedFormula());
		return result;
	}
	


	@Override
	public IPredicate determinize(Map<IPredicate, Set<IPredicate>> down2up) {
		if (!m_Pref.computeHoareAnnotation() && 
				m_Pref.determinization() != Determinization.STRONGESTPOST) {
			return m_SmtManager.newDontCarePredicate(null);
		}

		assert ((m_Pref.interprocedural() && 
				m_Pref.determinization() != Determinization.STRONGESTPOST)
				|| down2up.keySet().size() <= 1) : "more than one down state";

		List<IPredicate> upPredicates = new ArrayList<IPredicate>();
		for (IPredicate caller : down2up.keySet()) {
			for (IPredicate current : down2up.get(caller)) {
				if (SmtManager.isDontCare(current)) {
					return m_SmtManager.newDontCarePredicate(null);
				}
				upPredicates.add(current);
			}
		}
		TermVarsProc tvp = m_SmtManager.and(
									upPredicates.toArray(new IPredicate[0]));
		IPredicate result = m_SmtManager.newPredicate(tvp.getFormula(), 
				tvp.getProcedures(), tvp.getVars(), tvp.getClosedFormula());
		return result;
	}

	
	public IPredicate createSinkStateContent() {
		return m_SmtManager.newTruePredicate();
	}

	
	@Override
	public IPredicate createEmptyStackState(){
		return m_emtpyStack;
	}


	@Override
	public IPredicate createDoubleDeckerContent(IPredicate down,
			IPredicate up) {
		throw new UnsupportedOperationException();
	}

	
	@Override
	public IPredicate minimize(Collection<IPredicate> states) {
		TermVarsProc tvp = m_SmtManager.or(states.toArray(new IPredicate[0]));
		IPredicate result = m_SmtManager.newPredicate(tvp.getFormula(), 
				tvp.getProcedures(), tvp.getVars(), tvp.getClosedFormula());
		return result;
	}
	
	@Override
	public IPredicate senwa(IPredicate entry, IPredicate state) {
		assert false : "still used?";
		return m_SmtManager.newDontCarePredicate(((SPredicate) state).getProgramPoint());
	}


	@Override
	public IPredicate buchiComplementFKV(LevelRankingState compl) {
		return m_SmtManager.newDebugPredicate(compl.toString());
	}


	@Override
	public IPredicate intersectBuchi(IPredicate s1, IPredicate s2, int track) {
		return intersection(s1, s2);
	}
	
	
	
	
	
	
}
