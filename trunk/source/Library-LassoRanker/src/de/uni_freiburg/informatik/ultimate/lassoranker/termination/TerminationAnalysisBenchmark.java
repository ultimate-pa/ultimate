/*
 * Copyright (C) 2014-2015 Jan Leike (leike@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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

import de.uni_freiburg.informatik.ultimate.core.model.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.util.statistics.BaseStatisticsDataProvider;
import de.uni_freiburg.informatik.ultimate.util.statistics.DefaultMeasureDefinitions;
import de.uni_freiburg.informatik.ultimate.util.statistics.measures.StringCounter;

/**
 * Collects benchmarking information about the termination analysis
 * 
 * @author Matthias Heizmann
 */
public class TerminationAnalysisBenchmark extends BaseStatisticsDataProvider {

	@Statistics(type = DefaultMeasureDefinitions.STRING_COUNTER)
	private final StringCounter mConstraintsSatisfiability;

	@Statistics(type = DefaultMeasureDefinitions.STRING_COUNTER)
	private final StringCounter mTemplate;

	@Statistics(type = DefaultMeasureDefinitions.INT_COUNTER)
	private final int mVariablesStem;

	@Statistics(type = DefaultMeasureDefinitions.INT_COUNTER)
	private final int mVariablesLoop;

	@Statistics(type = DefaultMeasureDefinitions.INT_COUNTER)
	private final int mDisjunctsStem;

	@Statistics(type = DefaultMeasureDefinitions.INT_COUNTER)
	private final int mDisjunctsLoop;

	@Statistics(type = DefaultMeasureDefinitions.INT_COUNTER)
	private final int mDegree;

	@Statistics(type = DefaultMeasureDefinitions.INT_COUNTER)
	private final int mSupportingInvariants;

	@Statistics(type = DefaultMeasureDefinitions.INT_COUNTER)
	private final int mMotzkinApplications;

	@Statistics(type = DefaultMeasureDefinitions.LONG_TIME)
	private final long mTerminationAnalysisTime;

	public TerminationAnalysisBenchmark(final LBool constraintsSatisfiability, final int variablesStem,
			final int variablesLoop, final int disjunctsStem, final int disjunctsLoop, final String template,
			final int degree, final int supportingInvariants, final int motzkinApplications, final long time) {
		super((IToolchainStorage) null);
		mConstraintsSatisfiability = new StringCounter();
		mConstraintsSatisfiability.count(constraintsSatisfiability);
		mVariablesStem = variablesStem;
		mVariablesLoop = variablesLoop;
		mDisjunctsStem = disjunctsStem;
		mDisjunctsLoop = disjunctsLoop;
		mTemplate = new StringCounter();
		mTemplate.count(template);
		mDegree = degree;
		mSupportingInvariants = supportingInvariants;
		mMotzkinApplications = motzkinApplications;
		mTerminationAnalysisTime = time;
	}

}
