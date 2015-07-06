package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.TermVarsProc;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.ISLPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.util.HashRelation;

/**
 * 
 * @author musab@informatik.uni-freiburg.de
 *
 */
public class PredicateFactoryForInterpolantConsolidation extends PredicateFactory {
	
	private Map<IPredicate, Set<IPredicate>> m_locationsToSetOfPredicates;
	
	public PredicateFactoryForInterpolantConsolidation(SmtManager smtManager,
			TAPreferences taPrefs) {
		super(smtManager, taPrefs);
		m_locationsToSetOfPredicates = new HashMap<IPredicate, Set<IPredicate>>();
	}

	public Map<IPredicate, Set<IPredicate>> getLocationsToSetOfPredicates() {
		return m_locationsToSetOfPredicates;
	}

	@Override
	public IPredicate intersection(IPredicate p1, IPredicate p2) {
		// 1. Do the intersection
		assert (p1 instanceof ISLPredicate);
		
		ProgramPoint pp = ((ISLPredicate) p1).getProgramPoint();
		
		TermVarsProc tvp = super.m_SmtManager.and(p1, p2);
		IPredicate result = super.m_SmtManager.newSPredicate(pp, tvp);
		
		// 2. Store the predicates in the map
		if (m_locationsToSetOfPredicates.containsKey(p1)) {
			Set<IPredicate> predicates = m_locationsToSetOfPredicates.get(p1);
			predicates.add(p2);
		} else {
			Set<IPredicate> predicatesForThisLocation = new HashSet<IPredicate>();
			predicatesForThisLocation.add(p2);
			m_locationsToSetOfPredicates.put(p1, predicatesForThisLocation);
		}
		return result;
	}
}
