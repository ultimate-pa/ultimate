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

import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lassoranker.exceptions.TermException;
import de.uni_freiburg.informatik.ultimate.lassoranker.variables.ReplacementVar;
import de.uni_freiburg.informatik.ultimate.lassoranker.variables.ReplacementVarFactory;
import de.uni_freiburg.informatik.ultimate.lassoranker.variables.TransFormulaLR;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Util;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.ConstantFinder;


/**
 * Adds axioms to the stem and loop transition
 * 
 * @author Jan Leike
 */
public class AddAxioms extends TransitionPreProcessor {
	public static final String s_Description = "Add axioms to the transition";

	
	private final Term[] m_axioms;


	private final Set<ApplicationTerm> m_Constants = new HashSet<>();


	private final ReplacementVarFactory m_ReplacementVarFactory;
	
	/**
	 * @param axioms the axioms that should be added to stem and loop
	 */
	public AddAxioms(ReplacementVarFactory replacementVarFactory, Term[] axioms) {
		m_ReplacementVarFactory = replacementVarFactory;
		if (axioms == null) {
			m_axioms = new Term[0];
		} else {
			m_axioms = axioms;
		}
		for (Term axiom : m_axioms) {
			m_Constants.addAll((new ConstantFinder()).findConstants(axiom));
		}
	}
	
	@Override
	public TransFormulaLR process(Script script, TransFormulaLR tf) throws TermException {
		// Add constant variables as in- and outVars
		for (ApplicationTerm constVar : m_Constants) {
			ReplacementVar repVar = 
					m_ReplacementVarFactory.getOrConstuctReplacementVar(constVar); 
			tf.addInVar(repVar, constVar);
			tf.addOutVar(repVar, constVar);
		}
		Term formula = tf.getFormula();
		Term axioms = Util.and(script, m_axioms);
		formula = Util.and(script, formula, axioms);
		tf.setFormula(formula);
		return tf;
	}
	
	@Override
	public String getDescription() {
		return s_Description;
	}
}
