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
package de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.preprocessors;

import java.util.ArrayList;
import java.util.Collection;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Util;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.RankVarCollector;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.smt.ApplicationTermFinder;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.smt.ElimStore3.ArrayReadException;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.smt.ElimStore3.ArrayStoreDef;


/**
 * Replace term with arrays by term without arrays by introducing auxiliary
 * variables for all "important" array values and equalities that state the
 * constraints between array indices and array values (resp. the auxiliary
 * variables that replaced them). 
 * 
 * 
 * @author Matthias Heizmann
 */
public class RewriteArrays implements PreProcessor {
	private static final String s_AuxInPostfix  = "_in_array";
	private static final String s_AuxOutPostfix = "_out_array";
	
	/**
	 * The script used to transform the formula
	 */
	private Script m_Script;
	
	/**
	 * Collection of all generated auxiliary variables and the terms
	 * that they replace.
	 * These variables are *not* added to in- or outVars.
	 */
	private final Map<TermVariable, Term> m_auxVars;
	
	/**
	 * The auxiliary terms defining the auxiliary variables for the formula.
	 * These terms will be set in conjunction with the whole formula.
	 */
	private final Collection<Term> m_auxTerms;
	
	/**
	 * For generating auxiliary variables
	 */
	private final RankVarCollector m_rankVarCollector;
	
	/**
	 * Use assert statement to check if result is equivalent to the conjunction
	 * of input term and definition of auxiliary variables. 
	 */
	private static final boolean s_CheckResult = true;
	/**
	 * Use assert statement to check if the input is equivalent to the formula
	 * that is obtained by existentially quantifying each auxiliary variable in
	 * the result term.
	 */
	private static final boolean s_CheckResultWithQuantifiers = false;
	
	public RewriteArrays(RankVarCollector rankVarCollector) {
		m_rankVarCollector = rankVarCollector;
		m_auxVars = new LinkedHashMap<TermVariable, Term>();
		m_auxTerms = new ArrayList<Term>();
	}
	
	@Override
	public String getDescription() {
		return "Replace integer division by equivalent linear constraints";
	}
	
	@SuppressWarnings("unused")
	@Override
	public Term process(Script script, Term term) {
		assert m_Script == null;
		m_Script = script;
		
		Set<ApplicationTerm> storeTerms = 
				(new ApplicationTermFinder("store")).findMatchingSubterms(term);
		List<ArrayStoreDef> asds = new ArrayList<ArrayStoreDef>();
		for (Term storeTerm : storeTerms) {
			ArrayStoreDef asd;
			try {
				asd = new ArrayStoreDef(storeTerm);
			} catch (ArrayReadException e) {
				throw new UnsupportedOperationException("unexpected store term");
			}
			asds.add(asd);
		}
		
//			assert !s_CheckResult || !isIncorrect(term, result, auxTerm) 
//					: "rewrite division unsound";
//			assert !s_CheckResultWithQuantifiers
//					||	!isIncorrectWithQuantifiers(term, result, auxTerm) 
//					: "rewrite division unsound";
		return term;
	}
	
	/**
	 * Return true if we were able to prove that the result is incorrect.
	 * For this check we add to the input term the definition of the auxiliary
	 * variables.
	 */
	private boolean isIncorrect(Term input, Term result, Term auxTerm) {
		Term inputWithDefinitions = m_Script.term("and", input, auxTerm);
		return LBool.SAT == Util.checkSat(m_Script,
				m_Script.term("distinct",  inputWithDefinitions, result));
	}
	
	/**
	 * Return true if we were able to prove that the result is incorrect.
	 * For this check we existentially quantify auxiliary variables in the
	 * result term.
	 */
	private boolean isIncorrectWithQuantifiers(Term input, Term result,
			Term auxTerm) {
		Term quantified;
		if (m_auxVars.size() > 0) {
			quantified = m_Script.quantifier(Script.EXISTS,
					m_auxVars.keySet().toArray(new TermVariable[0]), result);
		} else {
			quantified = m_Script.term("true");
		}
		return Util.checkSat(m_Script, m_Script.term("distinct", 
				input, quantified)) == LBool.SAT;
	}
	
}