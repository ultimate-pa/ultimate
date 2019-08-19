/*
 * Copyright (C) 2014-2015 Jan Leike (leike@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE LassoRanker Library.
 * 
 * The ULTIMATE LassoRanker Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE LassoRanker Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE LassoRanker Library. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE LassoRanker Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE LassoRanker Library grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lassoranker;

import java.io.Serializable;
import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.icfgtransformer.transformulatransformers.TermException;
import de.uni_freiburg.informatik.ultimate.lassoranker.variables.InequalityConverter;
import de.uni_freiburg.informatik.ultimate.lassoranker.variables.InequalityConverter.NlaHandling;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transformations.ReplacementVarUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.ModifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;


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
 * @see de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormula
 */
public class LinearTransition implements Serializable {
	private static final long serialVersionUID = 8925538198614759883L;
	
	private final Map<IProgramVar, TermVariable> minVars;
	private final Map<IProgramVar, TermVariable> moutVars;
	
	private final List<List<LinearInequality>> mpolyhedra;
	private final boolean mcontains_integers;
	
	/**
	 * Construct a new LinearTransition
	 * @param polyhedra a list of polyhedra defining this transition
	 * @param inVars input variables
	 * @param outVars output variables
	 */
	public LinearTransition(final List<List<LinearInequality>> polyhedra,
			final Map<IProgramVar, TermVariable> inVars, final Map<IProgramVar, TermVariable> outVars) {
		assert(polyhedra != null);
		assert(inVars != null);
		assert(outVars != null);
		for (final List<LinearInequality> polyhedron : polyhedra) {
			assert(polyhedron != null);
		}
		mpolyhedra = polyhedra;
		minVars = Collections.unmodifiableMap(inVars);
		moutVars = Collections.unmodifiableMap(outVars);
		mcontains_integers = checkIfContainsSort(minVars.keySet(), "Int") || 
				checkIfContainsSort(moutVars.keySet(), "Int");
	}

	/**
	 * @return true iff varSet contain one or more variables of {@link Sort} 
	 * sortname.
	 */
	private boolean checkIfContainsSort(final Set<IProgramVar> varSet, final String sortname) {
		for (final IProgramVar rv : varSet) {
			final Sort sort = ReplacementVarUtils.getDefinition(rv).getSort(); 
			if (sort.getName().equals(sortname)) {
				return true;
			}
		}
		return false;
	}

	/**
	 * @return true iff there is at least one integer variable in mpolyhedra
	 */
	private boolean checkIfContainsIntegers() {
		for (final List<LinearInequality> polyhedron : mpolyhedra) {
			for (final LinearInequality ieq : polyhedron) {
				for (final Term var : ieq.getVariables()) {
					if (SmtSortUtils.isIntSort(var.getSort())) {
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
		final LinearInequality eqTrue = new LinearInequality();
		return new LinearTransition(
				Collections.singletonList(Collections.singletonList(eqTrue)),
				Collections.<IProgramVar, TermVariable> emptyMap(),
				Collections.<IProgramVar, TermVariable> emptyMap()
		);
	}
	
	/**
	 * @return the empty transition (0 < 0)
	 */
	public static LinearTransition getTranstionFalse() {
		final LinearInequality eqFalse = new LinearInequality();
		eqFalse.setStrict(true);
		return new LinearTransition(
				Collections.singletonList(Collections.singletonList(eqFalse)),
				Collections.<IProgramVar, TermVariable> emptyMap(),
				Collections.<IProgramVar, TermVariable> emptyMap()
		);
	}
	
	/**
	 * Convert a term into a list of clauses
	 * @param term a term in disjunctive normal form
	 * @return list of clauses
	 */
	private static List<Term> toClauses(final Term term) {
		final List<Term> l = new ArrayList<>();
		if (!(term instanceof ApplicationTerm)) {
			l.add(term);
			return l;
		}
		final ApplicationTerm appt = (ApplicationTerm) term;
		if (!appt.getFunction().getName().equals("or")) {
			l.add(term);
			return l;
		}
		for (final Term t : appt.getParameters()) {
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
	 * @param overapproxNonlinArithmetic 
	 * @param underapproxNonlinArithmetic 
	 * @param nlaHandling 
	 * @throws TermException if the supplied term does not have the correct form
	 */
	public static LinearTransition fromTransFormulaLR(final ModifiableTransFormula tf, 
			final NlaHandling nlaHandling)
			throws TermException {
		final List<List<LinearInequality>> polyhedra =
				new ArrayList<>();
		for (final Term disjunct : toClauses(tf.getFormula())) {
			polyhedra.add(InequalityConverter.convert(disjunct, nlaHandling));
		}
		return new LinearTransition(polyhedra, tf.getInVars(), tf.getOutVars());
	}
	
	/**
	 * @return the mapping between the trasition's input (unprimed) variables
	 *         and their representation as a TermVariable
	 */
	public Map<IProgramVar, TermVariable> getInVars() {
		return minVars;
	}
	
	/**
	 * @return the mapping between the trasition's output (primed) variables
	 *         and their representation as a TermVariable
	 */
	public Map<IProgramVar, TermVariable> getOutVars() {
		return moutVars;
	}
	
	/**
	 * @return whether this linear transition contains any integer variables
	 */
	public boolean containsIntegers() {
		return mcontains_integers;
	}
	
	/**
	 * Compute the integral hull of each polyhedron
	 */
	public void integralHull() {
		for (final List<LinearInequality> polyhedron : mpolyhedra) {
			polyhedron.addAll(IntegralHull.compute(polyhedron));
		}
	}
	
	/**
	 * @return whether this transition contains only one polyhedron
	 */
	public boolean isConjunctive() {
		return mpolyhedra.size() <= 1;
	}
	
	/**
	 * @return whether this transition is trivially true
	 */
	public boolean isTrue() {
		for (final List<LinearInequality> polyhedron : mpolyhedra) {
			boolean istrue = true;
			for (final LinearInequality li : polyhedron) {
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
		for (final List<LinearInequality> polyhedron : mpolyhedra) {
			boolean isfalse = false;
			for (final LinearInequality li : polyhedron) {
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
		return mpolyhedra.size();
	}
	
	/**
	 * @return the total number of inequalities in all polyhedra 
	 */
	public int getNumInequalities() {
		int num = 0;
		for (final List<LinearInequality> polyhedron : mpolyhedra) {
			num += polyhedron.size();
		}
		return num;
	}
	
	/**
	 * @return all variables occuring in any of the inequalities
	 */
	public Set<Term> getVariables() {
		final Set<Term> vars = new LinkedHashSet<>();
		for (final List<LinearInequality> polyhedron : mpolyhedra) {
			for (final LinearInequality li : polyhedron) {
				vars.addAll(li.getVariables());
			}
		}
		return vars;
	}
	
	/**
	 * @return this transition's polyhedra as a list
	 */
	public List<List<LinearInequality>> getPolyhedra() {
		return Collections.unmodifiableList(mpolyhedra);
	}
	
	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();
		
		// inVars and outVars
		sb.append("InVars: ");
		sb.append(minVars.toString());
		sb.append("\nOutVars: ");
		sb.append(moutVars.toString());
		
		// Transition polyhedron
		sb.append("\n(OR\n");
		for (final List<LinearInequality> polyhedron : mpolyhedra) {
			sb.append("    (AND\n");
			for (final LinearInequality ieq : polyhedron) {
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
