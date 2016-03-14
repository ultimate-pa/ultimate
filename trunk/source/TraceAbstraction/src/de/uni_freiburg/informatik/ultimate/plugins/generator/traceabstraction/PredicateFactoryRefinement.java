/*
 * Copyright (C) 2013-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE TraceAbstraction plug-in.
 * 
 * The ULTIMATE TraceAbstraction plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE TraceAbstraction plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceAbstraction plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceAbstraction plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE TraceAbstraction plug-in grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction;

import java.util.Collection;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.TermVarsProc;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.IMLPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.ISLPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.PredicateWithHistory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.HoareAnnotationPositions;

public class PredicateFactoryRefinement extends PredicateFactory {
	
	private static final boolean s_DebugComputeHistory = false;
	
	protected final Map<String,Map<String,ProgramPoint>> m_locNodes;
	protected int m_Iteration;
	protected final HoareAnnotationFragments m_HoareAnnotationFragments;
	private final boolean m_MaintainHoareAnnotationFragments = false;
	private final HashSet<ProgramPoint> m_HoareAnnotationPositions;
	
	
	public PredicateFactoryRefinement(Map<String,Map<String,ProgramPoint>> locNodes,
							SmtManager smtManager,
							TAPreferences taPrefs, 
							boolean maintainHoareAnnotationFragments, 
							HoareAnnotationFragments haf, 
							HashSet<ProgramPoint> hoareAnnotationPositions) {
		super(smtManager, taPrefs);
		m_locNodes = locNodes;
//		m_MaintainHoareAnnotationFragments = maintainHoareAnnotationFragments;
		m_HoareAnnotationFragments = haf;
		m_HoareAnnotationPositions = hoareAnnotationPositions;
	}

	
	public IPredicate intersection(IPredicate p1, IPredicate p2) {
		if (p1 instanceof IMLPredicate) {
//			assert m_SmtManager.isDontCare(p2);
			assert !m_Pref.computeHoareAnnotation();
			return m_SmtManager.newMLDontCarePredicate(((IMLPredicate) p1).getProgramPoints());
		}
		
		assert (p1 instanceof ISLPredicate);

		ProgramPoint pp = ((ISLPredicate) p1).getProgramPoint();

		if (omitComputationOfHoareAnnotation(pp, p1, p2)) {
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
	
	private boolean omitComputationOfHoareAnnotation(ProgramPoint pp, IPredicate p1, IPredicate p2) {
		if (!m_Pref.computeHoareAnnotation() || m_SmtManager.isDontCare(p1) || m_SmtManager.isDontCare(p2)) {
			return true;
		}
		if (m_Pref.getHoareAnnotationPositions() == HoareAnnotationPositions.LoopsAndPotentialCycles) {
			assert m_HoareAnnotationPositions != null : "we need this for HoareAnnotationPositions.LoopInvariantsAndEnsures";
			return !m_HoareAnnotationPositions.contains(pp);
		} else {
			return false;
		}
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
			TermVarsProc tvp = m_SmtManager.orWithSimplifyDDA(
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
