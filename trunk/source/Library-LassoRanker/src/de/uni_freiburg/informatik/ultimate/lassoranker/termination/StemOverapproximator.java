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
package de.uni_freiburg.informatik.ultimate.lassoranker.termination;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.core.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lassoranker.AnalysisType;
import de.uni_freiburg.informatik.ultimate.lassoranker.LassoRankerPreferences;
import de.uni_freiburg.informatik.ultimate.lassoranker.LinearInequality;
import de.uni_freiburg.informatik.ultimate.lassoranker.LinearTransition;
import de.uni_freiburg.informatik.ultimate.lassoranker.SMTSolver;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;


/**
 * Simplify the Lasso's Stem by creating an overapproximation.
 * Since this is an overapproximation, it can only be used for termination
 * analysis, not nontermination analysis.
 * 
 * The overapproximation works by only retaining those inequalities that
 * are implied by all disjuncts.
 * 
 * This method is generally incomplete.
 * 
 * @author Jan Leike
 */
class StemOverapproximator {
	private boolean m_annotate_terms;
	
	/**
	 * This setting makes the overapproximation somewhat better but also
	 * much slower.
	 */
	private static final boolean s_less_efficient_and_more_complete = false;
	
	/**
	 * This script is a new script of QF_LRA that belongs only to this object
	 */
	private Script m_script;
	
	/**
	 * Create a new StemOverapproximator
	 * @param preferences LassoRanker preferences regarding new SMT scripts
	 */
	public StemOverapproximator(LassoRankerPreferences preferences,
			IUltimateServiceProvider services, IToolchainStorage storage) {
		m_annotate_terms = preferences.annotate_terms;
		
		// Create a new QF_LRA script
		m_script = SMTSolver.newScript(preferences, "SimplifySIs", services, storage);
		m_script.setLogic(Logics.QF_LRA);
	}
	
	public LinearTransition overapproximate(LinearTransition stem) {
		Collection<LinearInequality> candidate_lis = new HashSet<LinearInequality>();
		if (s_less_efficient_and_more_complete) {
			// Add all linear inequalities occuring somewhere in the stem to the
			// list of candidates
			for (List<LinearInequality> polyhedron : stem.getPolyhedra()) {
				candidate_lis.addAll(polyhedron);
			}
		} else {
			candidate_lis.addAll(stem.getPolyhedra().get(0));
		}
		
		List<LinearInequality> new_stem = new ArrayList<LinearInequality>();
		for (LinearInequality candidate_li : candidate_lis) {
			// Check if stem -> candidate_li
			m_script.push(1);
			for (List<LinearInequality> polyhedron : stem.getPolyhedra()) {
				MotzkinTransformation motzkin = new MotzkinTransformation(m_script,
						AnalysisType.Linear, m_annotate_terms);
				motzkin.add_inequalities(polyhedron);
				LinearInequality li = candidate_li;
				li.negate();
				motzkin.add_inequality(li);
				motzkin.annotation = "stem implies candidate linear inequality";
				m_script.assertTerm(motzkin.transform(new Rational[0]));
			}
			if (m_script.checkSat().equals(LBool.SAT)) {
				new_stem.add(candidate_li);
			}
			m_script.pop(1);
		}
		
		return new LinearTransition(Collections.singletonList(new_stem),
				stem.getInVars(), stem.getOutVars());
	}
}
