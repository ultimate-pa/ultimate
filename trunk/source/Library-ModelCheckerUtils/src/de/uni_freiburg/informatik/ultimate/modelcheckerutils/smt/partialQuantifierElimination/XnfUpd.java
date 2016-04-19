/*
 * Copyright (C) 2014-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE ModelCheckerUtils Library.
 * 
 * The ULTIMATE ModelCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE ModelCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ModelCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ModelCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE ModelCheckerUtils Library grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.partialQuantifierElimination;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.services.model.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Util;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.util.DebugMessage;

public class XnfUpd extends XjunctPartialQuantifierElimination {
	

	public XnfUpd(Script script, IUltimateServiceProvider services) {
		super(script, services);
	}

	@Override
	public String getName() {
		return "unimportant select removal";
	}

	@Override
	public String getAcronym() {
		return "USR";
	}
	
	@Override
	public boolean resultIsXjunction() {
		return true;
	};

	@Override
	public Term[] tryToEliminate(int quantifier, Term[] parameters,
			Set<TermVariable> eliminatees) {
		final Set<TermVariable> occuringVars = new HashSet<TermVariable>();
		for (Term param : parameters) {
			occuringVars.addAll(Arrays.asList(param.getFreeVars()));
		}
		
		eliminatees.retainAll(occuringVars);

		final ConnectionPartition connection = new ConnectionPartition(Arrays.asList(parameters));
		final List<TermVariable> removeableTvs = new ArrayList<TermVariable>();
		final List<TermVariable> unremoveableTvs = new ArrayList<TermVariable>();
		final List<Term> removeableTerms = new ArrayList<Term>();
		final List<Term> unremoveableTerms = new ArrayList<Term>();
		for (Set<Term> connectedTerms : connection.getConnectedVariables()) {
			final Set<TermVariable> connectedVars = SmtUtils.getFreeVars(connectedTerms);
			final boolean isSuperfluous;
			if (quantifier == QuantifiedFormula.EXISTS) {
				final Term simplified = isSuperfluousConjunction(m_Script, connectedTerms, connectedVars, eliminatees);
				if (SmtUtils.isTrue(simplified)) {
					isSuperfluous = true;
				} else if (SmtUtils.isFalse(simplified)) {
					return new Term[] { simplified };
				} else if (simplified == null) {
					isSuperfluous = false;
				} else {
					throw new AssertionError("illegal case");
				}
			} else if (quantifier == QuantifiedFormula.FORALL) {
				final Term simplified = isSuperfluousDisjunction(m_Script, connectedTerms, connectedVars, eliminatees);
				if (SmtUtils.isFalse(simplified)) {
					isSuperfluous = true;
				} else if (SmtUtils.isTrue(simplified)) {
					return new Term[] { simplified };
				} else if (simplified == null) {
					isSuperfluous = false;
				} else {
					throw new AssertionError("illegal case");
				}
			} else {
				throw new AssertionError("unknown quantifier");
			}
			if (isSuperfluous) {
				removeableTvs.addAll(connectedVars);
				removeableTerms.addAll(connectedTerms);
			} else {
				unremoveableTvs.addAll(connectedVars);
				unremoveableTerms.addAll(connectedTerms);
			}
		}
		final List<Term> termsWithoutTvs = connection.getTermsWithOutTvs();
		assert occuringVars.size() == removeableTvs.size() + unremoveableTvs.size();
		assert parameters.length == removeableTerms.size() + unremoveableTerms.size() + termsWithoutTvs.size();
		for (Term termWithoutTvs : termsWithoutTvs) {
			LBool sat = Util.checkSat(m_Script, termWithoutTvs);
			if (sat == LBool.UNSAT) {
				if (quantifier == QuantifiedFormula.EXISTS) {
					eliminatees.clear();
					return new Term[] { m_Script.term("false") };
				} else if (quantifier == QuantifiedFormula.FORALL) {
					// we drop this term its equivalent to false
				} else {
					throw new AssertionError("unknown quantifier");
				}
			} else if (sat == LBool.SAT) {
				if (quantifier == QuantifiedFormula.EXISTS) {
					// we drop this term its equivalent to true
				} else if (quantifier == QuantifiedFormula.FORALL) {
					eliminatees.clear();
					return new Term[] { m_Script.term("true") };
				} else {
					throw new AssertionError("unknown quantifier");
				}
			} else {
				throw new AssertionError("expecting sat or unsat");
			}
		}
		if (removeableTerms.isEmpty()) {
			m_Logger.debug(new DebugMessage("not eliminated quantifier via UPD for {0}", occuringVars));
			return parameters;
		} else {
			eliminatees.removeAll(removeableTvs);
			m_Logger.debug(new DebugMessage("eliminated quantifier via UPD for {0}", removeableTvs));
			final Term[] result;
			if (unremoveableTerms.isEmpty()) {
				if (quantifier == QuantifiedFormula.EXISTS) {
					result = new Term[] { m_Script.term("true") };
				} else if (quantifier == QuantifiedFormula.FORALL) {
					result = new Term[] { m_Script.term("false") };
				} else {
					throw new AssertionError("unknown quantifier");
				}
			} else {
				result = unremoveableTerms.toArray(new Term[unremoveableTerms.size()]);
			}
			return result;
		}

	}
	
	
	
	/**
	 * Return "true" if connectedVars is a subset of quantifiedVars and the
	 * conjunction of terms is satisfiable.
	 * Return "false" if connectedVars is a subset of quantifiedVars and the
	 * conjunction of terms is not satisfiable.
	 * Return null otherwise
	 */
	public static Term isSuperfluousConjunction(Script script, Set<Term> terms, Set<TermVariable> connectedVars,
			Set<TermVariable> quantifiedVars) {
		if (quantifiedVars.containsAll(connectedVars)) {
			Term conjunction = Util.and(script, terms.toArray(new Term[terms.size()]));
			LBool isSat = Util.checkSat(script, conjunction);
			if (isSat == LBool.SAT) {
				return script.term("true");
			} else if (isSat == LBool.UNSAT) {
				return script.term("false");
			}
		}
		return null;
	}

	/**
	 * Return "false" if connectedVars is a subset of quantifiedVars and the
	 * conjunction of terms is not valid.
	 * Return "true" if connectedVars is a subset of quantifiedVars and the
	 * conjunction of terms is valid.
	 * Return null otherwise
	 */
	public static Term isSuperfluousDisjunction(Script script, Set<Term> terms, Set<TermVariable> connectedVars,
			Set<TermVariable> quantifiedVars) {
		if (quantifiedVars.containsAll(connectedVars)) {
			Term disjunction = Util.or(script, terms.toArray(new Term[terms.size()]));
			LBool isSat = Util.checkSat(script, Util.not(script, disjunction));
			if (isSat == LBool.SAT) {
				return script.term("false");
			} else if (isSat == LBool.UNSAT) {
				return script.term("true");
			}
		}
		return null;
	}
	
	

}
