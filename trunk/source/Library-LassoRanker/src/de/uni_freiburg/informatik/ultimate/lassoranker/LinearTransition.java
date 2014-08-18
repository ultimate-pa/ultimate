/*
 * Copyright (C) 2012-2014 University of Freiburg
 *
 * This file is part of the ULTIMATE LassoRanker Library.
 *
 * The ULTIMATE LassoRanker Library is free software: you can redistribute it
 * and/or modify it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation, either version 3 of the
 * License, or (at your option) any later version.
 *
 * The ULTIMATE LassoRanker Library is distributed in the hope that it will
 * be useful, but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE LassoRanker Library. If not,
 * see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE LassoRanker Library, or any covered work, by
 * linking or combining it with Eclipse RCP (or a modified version of
 * Eclipse RCP), containing parts covered by the terms of the Eclipse Public
 * License, the licensors of the ULTIMATE LassoRanker Library grant you
 * additional permission to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lassoranker;

import java.io.Serializable;
import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lassoranker.exceptions.TermException;
import de.uni_freiburg.informatik.ultimate.lassoranker.preprocessors.IntegralHull;
import de.uni_freiburg.informatik.ultimate.lassoranker.variables.InequalityConverter;
import de.uni_freiburg.informatik.ultimate.lassoranker.variables.RankVar;
import de.uni_freiburg.informatik.ultimate.lassoranker.variables.TransFormulaLR;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;


/**
 * A LinearTransition is a transition relation given as a finite union of
 * polyhedra.
 * 
 * There are two kinds of distinguished variables:
 * <li> inVars, (unprimed) input variables, and
 * <li> outVars, (primed) output variables.
 * 
 * Additionally, there might also be 'internal' variables that are neither
 * inVars, nor outVars.
 * 
 * The LinearTransition is LassoRanker's internal representation of
 * the TransFormula.
 * 
 * @author Jan Leike
 * @see de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.TransFormula
 */
public class LinearTransition implements Serializable {
	private static final long serialVersionUID = 8925538198614759883L;
	
	private final Map<RankVar, Term> m_inVars;
	private final Map<RankVar, Term> m_outVars;
	
	private final List<List<LinearInequality>> m_polyhedra;
	private final boolean m_contains_integers;
	
	/**
	 * Construct a new LinearTransition
	 * @param polyhedra a list of polyhedra defining this transition
	 * @param inVars input variables
	 * @param outVars output variables
	 */
	public LinearTransition(List<List<LinearInequality>> polyhedra,
			Map<RankVar, Term> inVars, Map<RankVar, Term> outVars) {
		assert(polyhedra != null);
		assert(inVars != null);
		assert(outVars != null);
		for (List<LinearInequality> polyhedron : polyhedra) {
			assert(polyhedron != null);
		}
		m_polyhedra = polyhedra;
		m_inVars = Collections.unmodifiableMap(inVars);
		m_outVars = Collections.unmodifiableMap(outVars);
		m_contains_integers = checkIfContainsIntegers();
	}
	
	/**
	 * @return true iff there is at least one integer variable in m_polyhedra
	 */
	private boolean checkIfContainsIntegers() {
		for (List<LinearInequality> polyhedron : m_polyhedra) {
			for (LinearInequality ieq : polyhedron) {
				for (Term var : ieq.getVariables()) {
					if (var.getSort().getName().equals("Int")) {
						return true;
					}
				}
			}
		}
		return false;
	}
	
//	/**
//	 * Check if a polyhedron is empty
//	 * @param script the solver used for the check
//	 * @return whether the polyhedron is empty
//	 */
//	private boolean isPolyhedronEmpty(Script script,
//			List<LinearInequality> polyhedron) {
//		script.push(1);
//		for (LinearInequality ieq : polyhedron) {
//			Term ieq_term = ieq.asTerm(script);
//			script.assertTerm(ieq_term);
//		}
//		boolean empty = script.checkSat() == LBool.UNSAT;
//		script.pop(1);
//		return empty;
//	}
	
	/**
	 * @return the maximal transition (0 <= 0)
	 */
	public static LinearTransition getTranstionTrue() {
		LinearInequality eqTrue = new LinearInequality();
		return new LinearTransition(
				Collections.singletonList(Collections.singletonList(eqTrue)),
				Collections.<RankVar, Term> emptyMap(),
				Collections.<RankVar, Term> emptyMap()
		);
	}
	
	/**
	 * @return the empty transition (0 < 0)
	 */
	public static LinearTransition getTranstionFalse() {
		LinearInequality eqFalse = new LinearInequality();
		eqFalse.setStrict(true);
		return new LinearTransition(
				Collections.singletonList(Collections.singletonList(eqFalse)),
				Collections.<RankVar, Term> emptyMap(),
				Collections.<RankVar, Term> emptyMap()
		);
	}
	
	/**
	 * Convert a term into a list of clauses
	 * @param term a term in disjunctive normal form
	 * @return list of clauses
	 */
	private static List<Term> toClauses(Term term) {
		List<Term> l = new ArrayList<Term>();
		if (!(term instanceof ApplicationTerm)) {
			l.add(term);
			return l;
		}
		ApplicationTerm appt = (ApplicationTerm) term;
		if (!appt.getFunction().getName().equals("or")) {
			l.add(term);
			return l;
		}
		for (Term t : appt.getParameters()) {
			l.addAll(toClauses(t));
		}
		return l;
	}
	
	/**
	 * Convert a TransFormulaLR in the proper form into a linear transition.
	 * 
	 * The transition formula must be in DNF, contain no negations, and only
	 * atoms of the form a <= b, a < b, a >= b, and a > b, with a and b being
	 * linear expressions, otherwise this method fails.
	 * 
	 * @param tf the transition formula
	 * @throws TermException if the supplied term does not have the correct form
	 */
	public static LinearTransition fromTransFormulaLR(TransFormulaLR tf)
			throws TermException {
		List<List<LinearInequality>> polyhedra =
				new ArrayList<List<LinearInequality>>();
		for (Term disjunct : toClauses(tf.getFormula())) {
			polyhedra.add(InequalityConverter.convert(disjunct));
		}
		return new LinearTransition(polyhedra, tf.getInVars(), tf.getOutVars());
	}
	
	/**
	 * @return the mapping between the trasition's input (unprimed) variables
	 *         and their representation as a TermVariable
	 */
	public Map<RankVar, Term> getInVars() {
		return m_inVars;
	}
	
	/**
	 * @return the mapping between the trasition's output (primed) variables
	 *         and their representation as a TermVariable
	 */
	public Map<RankVar, Term> getOutVars() {
		return m_outVars;
	}
	
	/**
	 * @return whether this linear transition contains any integer variables
	 */
	public boolean containsIntegers() {
		return m_contains_integers;
	}
	
	/**
	 * Compute the integral hull of each polyhedron
	 */
	public void integralHull() {
		for (List<LinearInequality> polyhedron : m_polyhedra) {
			polyhedron.addAll(IntegralHull.compute(polyhedron));
		}
	}
	
	/**
	 * @return whether this transition contains only one polyhedron
	 */
	public boolean isConjunctive() {
		return m_polyhedra.size() <= 1;
	}
	
	/**
	 * @return whether this transition is trivially true
	 */
	public boolean isTrue() {
		for (List<LinearInequality> polyhedron : m_polyhedra) {
			boolean istrue = true;
			for (LinearInequality li : polyhedron) {
				istrue = istrue && li.isConstant()
				                && li.getConstant().isZero()
				                && !li.isStrict();
			}
			if (istrue) {
				return true;
			}
		}
		return false;
	}
	
	/**
	 * @return whether this transition is trivially false
	 */
	public boolean isFalse() {
		for (List<LinearInequality> polyhedron : m_polyhedra) {
			boolean isfalse = false;
			for (LinearInequality li : polyhedron) {
				if (li.isConstant() && li.getConstant().isZero() && li.isStrict()) {
					isfalse = true;
					break;
				}
			}
			if (!isfalse) {
				return false;
			}
		}
		return true;
	}
	
	/**
	 * @return the number of polyhedra (number of disjuncts)
	 */
	public int getNumPolyhedra() {
		return m_polyhedra.size();
	}
	
	/**
	 * @return the total number of inequalities in all polyhedra 
	 */
	public int getNumInequalities() {
		int num = 0;
		for (List<LinearInequality> polyhedron : m_polyhedra) {
			num += polyhedron.size();
		}
		return num;
	}
	
	/**
	 * @return all variables occuring in any of the inequalities
	 */
	public Set<Term> getVariables() {
		Set<Term> vars = new LinkedHashSet<Term>();
		for (List<LinearInequality> polyhedron : m_polyhedra) {
			for (LinearInequality li : polyhedron) {
				vars.addAll(li.getVariables());
			}
		}
		return vars;
	}
	
	/**
	 * @return this transition's polyhedra as a list
	 */
	public List<List<LinearInequality>> getPolyhedra() {
		return Collections.unmodifiableList(m_polyhedra);
	}
	
	public String toString() {
		StringBuilder sb = new StringBuilder();
		
		// inVars and outVars
		sb.append("InVars: ");
		sb.append(m_inVars.toString());
		sb.append("\nOutVars: ");
		sb.append(m_outVars.toString());
		
		// Transition polyhedron
		sb.append("\n(OR\n");
		for (List<LinearInequality> polyhedron : m_polyhedra) {
			sb.append("    (AND\n");
			for (LinearInequality ieq : polyhedron) {
				sb.append("        ");
				sb.append(ieq);
				sb.append("\n");
			}
			sb.append("    )\n");
		}
		sb.append(")");
		return sb.toString();
	}
}
