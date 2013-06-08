package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.preferences.TAPreferences.Determinization;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.ISLPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.PredicateWithHistory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager.TermVarsProc;

public class PredicateFactoryRefinement extends PredicateFactory {
	
	private static final boolean s_DebugComputeHistory = false;
	
	protected final Map<String,Map<String,ProgramPoint>> m_locNodes;
	protected int m_Iteration;
	protected final HoareAnnotationFragments m_HoareAnnotationFragments;
	private final boolean m_MaintainHoareAnnotationFragments;
	
	
	public PredicateFactoryRefinement(Map<String,Map<String,ProgramPoint>> locNodes,
							SmtManager smtManager,
							TAPreferences taPrefs, 
							boolean maintainHoareAnnotationFragments, 
							HoareAnnotationFragments haf) {
		super(smtManager, taPrefs);
		m_locNodes = locNodes;
		m_MaintainHoareAnnotationFragments = maintainHoareAnnotationFragments;
		m_HoareAnnotationFragments = haf;
	}

	
	public IPredicate intersection(IPredicate p1, IPredicate p2) {
		assert (p1 instanceof ISLPredicate);

		ProgramPoint pp = ((ISLPredicate) p1).getProgramPoint();

		if (!m_Pref.computeHoareAnnotation() || SmtManager.isDontCare(p1) || SmtManager.isDontCare(p2)) {
			return m_SmtManager.newDontCarePredicate(pp);
		}
		TermVarsProc tvp = m_SmtManager.and(p1, p2);
		IPredicate result;
		if (s_DebugComputeHistory) {
			assert (p1 instanceof PredicateWithHistory);
			Map<Integer, Term> history = 
					((PredicateWithHistory) p1).getCopyOfHistory();
				history.put(m_Iteration,p2.getFormula());
			result = m_SmtManager.newPredicateWithHistory(
					pp,
					tvp.getFormula(),
					tvp.getProcedures(),
					tvp.getVars(),
					tvp.getClosedFormula(),
					history);
		} else {
			result = m_SmtManager.newSPredicate(pp, tvp.getFormula(), 
					tvp.getProcedures(), tvp.getVars(), tvp.getClosedFormula());
		}
		
		if (m_MaintainHoareAnnotationFragments) {
			m_HoareAnnotationFragments.announceReplacement(p1, result);
		}
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

	@Override
	public IPredicate minimize(Collection<IPredicate> states) {
		assert sameProgramPoints(states);
		IPredicate someElement = states.iterator().next();
		ProgramPoint pp = ((ISLPredicate) someElement).getProgramPoint();
		if (states.isEmpty()) {
			assert false : "minimize empty set???";
			return m_SmtManager.newDontCarePredicate(pp);
		}
		TermVarsProc tvp = m_SmtManager.or(
				states.toArray(new IPredicate[0]));
		if (tvp.getFormula() == SmtManager.getDontCareTerm()) {
			return m_SmtManager.newDontCarePredicate(pp);
		} else {
			return m_SmtManager.newSPredicate(pp, tvp.getFormula(), 
					tvp.getProcedures(), tvp.getVars(), tvp.getClosedFormula());
		}
	}
	
	
	private static boolean sameProgramPoints(Collection<IPredicate> states) {
		Iterator<IPredicate> it = states.iterator();
		IPredicate firstPredicate = it.next();
		ProgramPoint firstProgramPoint = ((ISLPredicate) firstPredicate).getProgramPoint();
		while (it.hasNext()) {
			ProgramPoint pp = ((ISLPredicate) it.next()).getProgramPoint();
			if (pp != firstProgramPoint) {
				return false;
			}
		}
		return true;
	}
	

	@Override
	public IPredicate senwa(IPredicate entry, IPredicate state) {
		return m_SmtManager.newDontCarePredicate(((SPredicate) state).getProgramPoint());
	}
	
	@Override
	public IPredicate intersectBuchi(IPredicate s1, IPredicate s2, int track) {
		return intersection(s1, s2);
	}


	public void setIteration(int i) {
		m_Iteration = i;
	}
}
