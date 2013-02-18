package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.ResultChecker;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.preferences.TAPreferences.Determinization;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.ISLPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.PredicateWithHistory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager.TermVarsProc;

public class TAContentFactory extends StateFactory<IPredicate> {
	
	private static final boolean s_DebugComputeHistory = false;
	
	protected Map<String,Map<String,ProgramPoint>> m_locNodes;
	protected AbstractCegarLoop m_AbstractCegarLoop;
	protected Script m_Script;
	final protected TAPreferences m_Pref;
	
	private final IPredicate m_emtpyStack; 
	
	public HoareAnnotationFragments m_HoareAnnotationFragments;
	/**
	 * True iff we are in a refinement operation right now.
	 */
	protected boolean m_RefinementOperation;
	protected final SmtManager m_SmtManager;
	
	
	public TAContentFactory(Map<String,Map<String,ProgramPoint>> locNodes,
							AbstractCegarLoop abstractCegarLoop,
							SmtManager smtManager,
							TAPreferences taPrefs) {
		m_locNodes = locNodes;
		m_AbstractCegarLoop = abstractCegarLoop;
		m_Pref = taPrefs;
		m_Script = smtManager.getScript();
		m_SmtManager = smtManager;

		Term emptyStack = m_Script.variable("emptyStack",m_Script.sort("Bool"));
		ProgramPoint pp = new ProgramPoint("noCaller", "noCaller", false, null, null, m_Script);
		m_emtpyStack = m_SmtManager.newSPredicate(pp, emptyStack, new String[0], new HashSet<BoogieVar>(0), emptyStack);
	}

	
	/**
	 * Return true iff the current operation is a used in a check of the 
	 * automata library to verify the result.
	 * (In this case we must not store use the constructed states for the Hoare
	 * annotation. 
	 */
	public boolean isAutomataLibraryResultCheck() {
		return ResultChecker.doingInvariantCheck();		
	}
	

	public IPredicate intersection(IPredicate p1, IPredicate p2) {

		ProgramPoint pp = null;
		if (p1 instanceof ISLPredicate) {
			pp = ((ISLPredicate) p1).getProgramPoint();			
		}
		if (!m_Pref.computeHoareAnnotation() || SmtManager.isDontCare(p1) || SmtManager.isDontCare(p2)) {
			return m_SmtManager.newDontCarePredicate(pp);
		}
		TermVarsProc tvp = m_AbstractCegarLoop.getSmtManager().and(p1, p2);
		IPredicate result;
		if (p1 instanceof PredicateWithHistory) {
			Map<Integer, Term> history = 
					((PredicateWithHistory) p1).getCopyOfHistory();
				history.put(m_AbstractCegarLoop.getIteration(),p2.getFormula());
			result = m_SmtManager.newPredicateWithHistory(
					pp,
					tvp.getFormula(),
					tvp.getProcedures(),
					tvp.getVars(),
					tvp.getClosedFormula(),
					history);
		} else if (p1 instanceof ISLPredicate) {
			assert !(p1 instanceof PredicateWithHistory);
			result = m_SmtManager.newSPredicate(pp, tvp.getFormula(), 
					tvp.getProcedures(), tvp.getVars(), tvp.getClosedFormula());
		} else {
			result = m_SmtManager.newPredicate(tvp.getFormula(), 
					tvp.getProcedures(), tvp.getVars(), tvp.getClosedFormula());
		}
		
		if (!isAutomataLibraryResultCheck() && m_HoareAnnotationFragments !=null) {
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

	
	/**
	 * Announce that a refinement operation starts. Specify the Hoare
	 * annotation which has to be updated during the refinement.
	 */
	public void beginRefinementOperation(HoareAnnotationFragments haf) {
		m_RefinementOperation = true;
		m_HoareAnnotationFragments = haf;
	}

	
	/**
	 * Announce that a refinement operation is finished. Remove Hoare
	 * annotation, so that it is not touched in further non-refinement
	 * operations (e.g. automata operation correctness checks).
	 */
	public void refinementOperationFinished() {
		m_RefinementOperation = false;
		m_HoareAnnotationFragments = null;
	}

	
	@Override
	public IPredicate minimize(Collection<IPredicate> states) {
		if (states.isEmpty()) {
			assert false : "minimize empty set???";
			return m_SmtManager.newDontCarePredicate(null);
		}
		TermVarsProc tvp = m_AbstractCegarLoop.getSmtManager().or(
				states.toArray(new IPredicate[0]));
		ProgramPoint pp = null;
		IPredicate someElement = states.iterator().next();
		if (someElement instanceof ISLPredicate) {
			pp = ((ISLPredicate) someElement).getProgramPoint();
		}
		if (tvp.getFormula() == SmtManager.m_DontCareTerm) {
			return m_SmtManager.newDontCarePredicate(null);
		} else {
			if (pp == null) {
				return m_SmtManager.newPredicate(tvp.getFormula(), 
						tvp.getProcedures(), tvp.getVars(), tvp.getClosedFormula());
			} else {
				return m_SmtManager.newSPredicate(pp, tvp.getFormula(), 
						tvp.getProcedures(), tvp.getVars(), tvp.getClosedFormula());
			}
		}
	}
	
	
	private boolean sameProgramPoints(Collection<IPredicate> states) {
		Iterator<IPredicate> it = states.iterator();
		IPredicate firstPredicate = it.next();
		ProgramPoint firstProgramPoint = ((SPredicate) firstPredicate).getProgramPoint();
		while (it.hasNext()) {
			ProgramPoint pp = ((SPredicate) it.next()).getProgramPoint();
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
}
