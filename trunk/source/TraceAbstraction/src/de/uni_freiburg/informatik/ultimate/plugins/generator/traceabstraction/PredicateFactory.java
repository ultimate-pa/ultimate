package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.buchiNwa.BuchiComplementFKVNwa.LevelRankingState;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.TermVarsProc;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.IMLPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.ISLPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences.InterpolantAutomatonEnhancement;

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
		throw new AssertionError(
				"intersect is only required for refinement, not for construction of interpolant automaton");
	}
	


	@Override
	public IPredicate determinize(Map<IPredicate, Set<IPredicate>> down2up) {
		if (m_Pref.computeHoareAnnotation()) {
			assert ((m_Pref.interprocedural())
					|| down2up.keySet().size() <= 1) : "more than one down state";

			List<IPredicate> upPredicates = new ArrayList<IPredicate>();
			for (IPredicate caller : down2up.keySet()) {
				for (IPredicate current : down2up.get(caller)) {
					if (m_SmtManager.isDontCare(current)) {
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
		} else {
			return m_SmtManager.newDontCarePredicate(null);
		}
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
		throw new AssertionError(
				"intersect is only required for refinement, not for construction of interpolant automaton");
	}
	
	
	
	
	@Override
	public IPredicate getContentOnConcurrentProduct(IPredicate c1,
			IPredicate c2) {
		if (!(c2 instanceof ISLPredicate)) {
			throw new IllegalArgumentException(
					"has to be predicate with single location");
		}
		ProgramPoint[] programPoints;
		if (c1 instanceof ISLPredicate) {
			programPoints = new ProgramPoint[2];
			programPoints[0] = ((ISLPredicate) c1).getProgramPoint();
		} else if (c1 instanceof IMLPredicate) {
			IMLPredicate mlpred = (IMLPredicate) c1;
			int newLength = mlpred.getProgramPoints().length + 1;
			programPoints = Arrays.copyOf(mlpred.getProgramPoints(), newLength);
		} else {
			throw new UnsupportedOperationException();
		}
		ProgramPoint c2PP = ((ISLPredicate) c2).getProgramPoint();
		programPoints[programPoints.length-1] = c2PP;
		TermVarsProc tvp = m_SmtManager.and(c1, c2);
		IMLPredicate result = m_SmtManager.newMLPredicate(programPoints, tvp);
		return result;
	}
	
	
}
