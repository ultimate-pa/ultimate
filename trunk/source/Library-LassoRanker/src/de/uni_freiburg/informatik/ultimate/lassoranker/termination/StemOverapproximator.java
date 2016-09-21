/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
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
package de.uni_freiburg.informatik.ultimate.lassoranker.termination;

import java.io.IOException;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.core.model.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
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
 * Simplify the Lasso's Stem by creating an overapproximation. Since this is an
 * overapproximation, it can only be used for termination analysis, not
 * nontermination analysis.
 * 
 * The overapproximation works by selecting inequalities from the stem that are
 * implied by all disjuncts:
 * 
 * new_stem = /\ { ineq ∈ old_stem | old_stem -> ineq }
 * 
 * This method is generally incomplete.
 * 
 * @author Jan Leike
 */
class StemOverapproximator {
	private final boolean mannotate_terms;

	/**
	 * This setting makes the overapproximation somewhat better but also much
	 * slower.
	 */
	private static final boolean s_less_efficient_and_more_complete = false;

	/**
	 * If approximation fails, return the transition 'true'. If this is set to
	 * false, the original transition will be returned.
	 */
	private static final boolean s_return_true_if_approximation_fails = false;

	/**
	 * This script is a new script of QF_LRA that belongs only to this object
	 */
	private Script mscript;

	/**
	 * Create a new StemOverapproximator
	 * 
	 * @param preferences
	 *            LassoRanker preferences regarding new SMT scripts
	 * @throws IOException
	 */
	public StemOverapproximator(LassoRankerPreferences preferences, IUltimateServiceProvider services,
			IToolchainStorage storage) throws IOException {
		mannotate_terms = preferences.mAnnotateTerms;

		// Create a new QF_LRA script
		mscript = SMTSolver.newScript(preferences, "SimplifySIs", services, storage);
		mscript.setLogic(Logics.QF_LRA);
	}

	@Override
	protected void finalize() throws Throwable {
		if (mscript != null) {
			mscript.exit();
			mscript = null;
		}
		super.finalize();
	}

	public LinearTransition overapproximate(LinearTransition stem) {
		if (stem.getNumPolyhedra() < 2) {
			return stem; // nothing to do
		}

		final Collection<LinearInequality> candidate_lis = new HashSet<LinearInequality>();
		if (s_less_efficient_and_more_complete) {
			// Add all linear inequalities occuring somewhere in the stem to the
			// list of candidates
			for (final List<LinearInequality> polyhedron : stem.getPolyhedra()) {
				candidate_lis.addAll(polyhedron);
			}
		} else {
			candidate_lis.addAll(stem.getPolyhedra().get(0));
			candidate_lis.addAll(stem.getPolyhedra().get(1));
		}

		final List<LinearInequality> new_stem = new ArrayList<LinearInequality>();
		for (final LinearInequality candidate_li : candidate_lis) {
			// Check if stem -> candidate_li
			mscript.push(1);
			for (final List<LinearInequality> polyhedron : stem.getPolyhedra()) {
				final MotzkinTransformation motzkin = new MotzkinTransformation(mscript, AnalysisType.Linear,
						mannotate_terms);
				motzkin.add_inequalities(polyhedron);
				final LinearInequality li = new LinearInequality(candidate_li);
				li.negate();
				motzkin.add_inequality(li);
				motzkin.annotation = "stem implies candidate linear inequality";
				mscript.assertTerm(motzkin.transform(new Rational[0]));
			}
			if (mscript.checkSat().equals(LBool.SAT)) {
				new_stem.add(candidate_li);
			}
			mscript.pop(1);
		}

		if (new_stem.isEmpty()) {
			if (s_return_true_if_approximation_fails) {
				return LinearTransition.getTranstionTrue();
			} else {
				return stem;
			}
		} else {
			return new LinearTransition(Collections.singletonList(new_stem), stem.getInVars(), stem.getOutVars());
		}
	}
}
