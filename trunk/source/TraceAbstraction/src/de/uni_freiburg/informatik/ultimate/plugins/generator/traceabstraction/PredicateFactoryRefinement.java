package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.IMLPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.ISLPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.PredicateWithHistory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager.TermVarsProc;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences.Determinization;

public class PredicateFactoryRefinement extends PredicateFactory {
	
	private static final boolean s_DebugComputeHistory = false;
	
	protected final Map<String,Map<String,ProgramPoint>> m_locNodes;
	protected int m_Iteration;
	protected final HoareAnnotationFragments m_HoareAnnotationFragments;
	private final boolean m_MaintainHoareAnnotationFragments = false;
	
	
	public PredicateFactoryRefinement(Map<String,Map<String,ProgramPoint>> locNodes,
							SmtManager smtManager,
							TAPreferences taPrefs, 
							boolean maintainHoareAnnotationFragments, 
							HoareAnnotationFragments haf) {
		super(smtManager, taPrefs);
		m_locNodes = locNodes;
//		m_MaintainHoareAnnotationFragments = maintainHoareAnnotationFragments;
		m_HoareAnnotationFragments = haf;
	}

	
	public IPredicate intersection(IPredicate p1, IPredicate p2) {
		if (p1 instanceof IMLPredicate) {
			assert SmtManager.isDontCare(p2);
			assert !m_Pref.computeHoareAnnotation();
			return m_SmtManager.newMLDontCarePredicate(((IMLPredicate) p1).getProgramPoints());
		}
		
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
			result = m_SmtManager.newSPredicate(pp, tvp);
		}
		
		if (m_MaintainHoareAnnotationFragments) {
//			m_HoareAnnotationFragments.announceReplacement(p1, result);
		}
		return result;
	}
	


	@Override
	public IPredicate determinize(Map<IPredicate, Set<IPredicate>> down2up) {
		throw new AssertionError(
				"determinize is only required for construction of interpolant automaton, not for refinement");
	}

	@Override
	public IPredicate minimize(Collection<IPredicate> states) {
		assert sameProgramPoints(states);
		IPredicate someElement = states.iterator().next();
		if (someElement instanceof ISLPredicate) {
			ProgramPoint pp = ((ISLPredicate) someElement).getProgramPoint();
			if (states.isEmpty()) {
				assert false : "minimize empty set???";
			return m_SmtManager.newDontCarePredicate(pp);
			}
			TermVarsProc tvp = m_SmtManager.or(
					states.toArray(new IPredicate[0]));
			if (tvp.getFormula() == m_SmtManager.getDontCareTerm()) {
				return m_SmtManager.newDontCarePredicate(pp);
			} else {
				return m_SmtManager.newSPredicate(pp, tvp);
			}
		} else if (someElement instanceof IMLPredicate) {
			ProgramPoint[] pps = ((IMLPredicate) someElement).getProgramPoints();
			if (states.isEmpty()) {
				assert false : "minimize empty set???";
			return m_SmtManager.newMLDontCarePredicate(pps);
			}
			TermVarsProc tvp = m_SmtManager.or(
					states.toArray(new IPredicate[0]));
			if (tvp.getFormula() == m_SmtManager.getDontCareTerm()) {
				return m_SmtManager.newMLDontCarePredicate(pps);
			} else {
				return m_SmtManager.newMLPredicate(pps, tvp);
			}
		} else {
			throw new AssertionError("unknown predicate");
		}
	}
	
	
	private static boolean sameProgramPoints(Collection<IPredicate> states) {
		Iterator<IPredicate> it = states.iterator();
		IPredicate firstPredicate = it.next();
		if (firstPredicate instanceof ISLPredicate) {
			ProgramPoint firstProgramPoint = ((ISLPredicate) firstPredicate).getProgramPoint();
			while (it.hasNext()) {
				ProgramPoint pp = ((ISLPredicate) it.next()).getProgramPoint();
				if (pp != firstProgramPoint) {
					return false;
				}
			}
		} else if (firstPredicate instanceof IMLPredicate) {
			System.out.println("Warning, check not implemented");
		} else {
			throw new AssertionError("unsupported predicate");
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
