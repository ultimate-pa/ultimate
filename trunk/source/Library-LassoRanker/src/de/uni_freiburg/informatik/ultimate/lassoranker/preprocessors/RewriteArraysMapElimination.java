/*
 * Copyright (C) 2014-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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
package de.uni_freiburg.informatik.ultimate.lassoranker.preprocessors;

import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lassoranker.exceptions.TermException;
import de.uni_freiburg.informatik.ultimate.lassoranker.mapelimination.MapEliminator;
import de.uni_freiburg.informatik.ultimate.lassoranker.variables.LassoUnderConstruction;
import de.uni_freiburg.informatik.ultimate.lassoranker.variables.TransFormulaLR;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Boogie2SMT;

/**
 * Replace term with arrays by term without arrays by introducing replacement
 * variables for all "important" array values and equalities that state the
 * constraints between array indices and array values (resp. their replacement
 * variables).
 *
 *
 * @author Frank Schüssele
 */
public class RewriteArraysMapElimination extends LassoPreprocessor {

	private final IUltimateServiceProvider mServices;

	public static final String s_Description =
			"Removes arrays by introducing new variables for each relevant array cell";

	private final Boogie2SMT mBoogie2smt;


	public RewriteArraysMapElimination(final IUltimateServiceProvider services, final Boogie2SMT boogie2smt) {
		mServices = services;
		mBoogie2smt = boogie2smt;
	}

	@Override
	public String getName() {
		return getClass().getSimpleName();
	}

	@Override
	public String getDescription() {
		return s_Description;
	}

	@Override
	public Collection<LassoUnderConstruction> process(final LassoUnderConstruction lasso) throws TermException {
		// TODO: Only basic version, do other things like IndexSupportingInvariantAnalysis
		final MapEliminator elim = new MapEliminator(mServices, mBoogie2smt, Arrays.asList(lasso.getStem(), lasso.getLoop()));
		final TransFormulaLR newStem = elim.getArrayFreeTransFormula(lasso.getStem());
		final TransFormulaLR newLoop = elim.getArrayFreeTransFormula(lasso.getLoop());
		final LassoUnderConstruction newLasso = new LassoUnderConstruction(newStem, newLoop);
		return Collections.singleton(newLasso);
	}
}
