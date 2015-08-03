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
package de.uni_freiburg.informatik.ultimate.lassoranker.preprocessors;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.lassoranker.variables.RankVar;
import de.uni_freiburg.informatik.ultimate.lassoranker.variables.ReplacementVarFactory;
import de.uni_freiburg.informatik.ultimate.lassoranker.variables.TransFormulaLR;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Util;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Boogie2SMT;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Boogie2SmtSymbolTable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SafeSubstitution;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;

/**
 * Some static methods for TransFormulaLR 
 * 
 * @author Matthias Heizmann
 */
public class TransFormulaUtils {



	public static boolean allVariablesAreInVars(List<Term> terms, TransFormulaLR tf) {
		for (Term term : terms) {
			if (!allVariablesAreInVars(term, tf)) {
				return false;
			}
		}
		return true;
	}

	public static boolean allVariablesAreOutVars(List<Term> terms, TransFormulaLR tf) {
		for (Term term : terms) {
			if (!allVariablesAreOutVars(term, tf)) {
				return false;
			}
		}
		return true;
	}
	
	public static boolean allVariablesAreVisible(List<Term> terms, TransFormulaLR tf) {
		for (Term term : terms) {
			if (!allVariablesAreVisible(term, tf)) {
				return false;
			}
		}
		return true;
	}

	public static boolean allVariablesAreInVars(Term term, TransFormulaLR tf) {
		for (TermVariable tv : term.getFreeVars()) {
			if (!isInvar(tv, tf)) {
				return false;
			}
		}
		return true;
	}

	public static boolean allVariablesAreOutVars(Term term, TransFormulaLR tf) {
		for (TermVariable tv : term.getFreeVars()) {
			if (!isOutvar(tv, tf)) {
				return false;
			}
		}
		return true;
	}
	
	public static boolean allVariablesAreVisible(Term term, TransFormulaLR tf) {
		for (TermVariable tv : term.getFreeVars()) {
			if (isVisible(tv, tf)) {
				// do nothing
			} else {
				return false;
			}
		}
		return true;
	}

	private static boolean isVisible(TermVariable tv, TransFormulaLR tf) {
		return tf.getOutVarsReverseMapping().keySet().contains(tv) || 
				tf.getInVarsReverseMapping().keySet().contains(tv);
	}

	public static boolean isInvar(TermVariable tv, TransFormulaLR tf) {
		return tf.getInVarsReverseMapping().keySet().contains(tv);
	}

	public static boolean isOutvar(TermVariable tv, TransFormulaLR tf) {
		return tf.getOutVarsReverseMapping().keySet().contains(tv);
	}
	
	public static boolean isVar(TermVariable tv, TransFormulaLR tf) {
		return tf.getOutVarsReverseMapping().keySet().contains(tv);
	}
	
	
	public static Term renameToInVars(Script script, ReplacementVarFactory rvf, Boogie2SmtSymbolTable symbTab, TransFormulaLR tf, Term term) {
		return renameToVars(script, rvf, symbTab, term, tf.getInVars());
	}
	public static Term renameToOutVars(Script script, ReplacementVarFactory rvf, Boogie2SmtSymbolTable symbTab, TransFormulaLR tf, Term term) {
		return renameToVars(script, rvf, symbTab, term, tf.getInVars());
	}

	private static Term renameToVars(Script script, ReplacementVarFactory rvf,
			Boogie2SmtSymbolTable symbTab, Term term,
			Map<RankVar, Term> varMapping) {
		Map<Term, Term> substitutionMapping = new HashMap<>();
		for (TermVariable tv : term.getFreeVars()) {
			BoogieVar bv = symbTab.getBoogieVar(tv);
			if (bv == null) {
				throw new IllegalArgumentException("term contains unknown variable");
			}
			RankVar rv = rvf.getOrConstuctBoogieVarWrapper(bv);
			Term substituent = varMapping.get(rv);
			substitutionMapping.put(tv, substituent);
		}
		Term result = (new SafeSubstitution(script, substitutionMapping)).transform(term);
		return result;
	}
	
	/**
	 * Compute the RankVar of a given TermVariable and return its definition. 
	 */
	public static Term getDefinition(TransFormulaLR tf, TermVariable tv) {
		RankVar rv = tf.getInVarsReverseMapping().get(tv);
		if (rv == null) {
			rv = tf.getOutVarsReverseMapping().get(tv);
		}
		if (rv == null) {
			return null;
		}
		return rv.getDefinition();
	}
	
	/**
	 * Compute the RankVar for each TermVariable that occurs in the Term term.
	 * Return a term in which each TermVarialbe is substituted by the definition
	 * of the RankVar.
	 * Throws an IllegalArgumentException if there occurs term contains a
	 * TermVariable that does not have a RankVar (e.g., an auxiliary variable).
	 */
	public static Term translateTermVariablesToDefinitions(Script script, 
			TransFormulaLR tf, Term term) {
		Map<Term, Term> substitutionMapping = new HashMap<Term, Term>();
		for (TermVariable tv : term.getFreeVars()) {
			Term definition = getDefinition(tf, tv);
			if (definition == null) {
				throw new IllegalArgumentException(tv + "has no RankVar");
			}
			substitutionMapping.put(tv, definition);
		}
		return (new SafeSubstitution(script, substitutionMapping)).transform(term);
	}


	
	public static List<Term> translateTermVariablesToDefinitions(Script script, 
			TransFormulaLR tf, List<Term> terms) {
		List<Term> result = new ArrayList<Term>();
		for (Term term : terms) {
			result.add(translateTermVariablesToDefinitions(script, tf, term));
		}
		return result;
	}
	
	
	public static boolean inVarAndOutVarCoincide(RankVar rv, TransFormulaLR rf) {
		return rf.getInVars().get(rv) == rf.getOutVars().get(rv);
	}


	public static LBool transFormulaImplication(Script script, TransFormulaLR antecedent, TransFormulaLR consequent) {
		throw new UnsupportedOperationException("not yet implemented");
//		Term ant1 = translateTermVariablesToDefinitions(script, antecedent, antecedent.getFormula());
//		Term con1 = translateTermVariablesToDefinitions(script, consequent, consequent.getFormula());
//		Term negatedCon = Util.not(script, con1);
//		Term conjunction = Util.and(script, ant1, negatedCon);
//		LBool result = Util.checkSat(script, conjunction);
////		script.push(1);
////		script.assertTerm(ant1);
////		script.assertTerm(negatedCon);
////		LBool result = script.checkSat();
////		script.pop(1);
//		return result;
	}


}