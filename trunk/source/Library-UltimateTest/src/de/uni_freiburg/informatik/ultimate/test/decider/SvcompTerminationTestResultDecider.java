/*
 * Copyright (C) 2021 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 20216 University of Freiburg
 *
 * This file is part of the ULTIMATE UnitTest Library.
 *
 * The ULTIMATE UnitTest Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE UnitTest Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE UnitTest Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE UnitTest Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE UnitTest Library grant you additional permission
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.test.decider;

import de.uni_freiburg.informatik.ultimate.test.UltimateRunDefinition;
import de.uni_freiburg.informatik.ultimate.test.decider.expectedresult.IExpectedResultFinder;
import de.uni_freiburg.informatik.ultimate.test.decider.expectedresult.YamlBasedExpectedResultFinder;
import de.uni_freiburg.informatik.ultimate.test.decider.overallresult.TerminationAnalysisOverallResult;
import de.uni_freiburg.informatik.ultimate.test.util.TestUtil;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap2;

/**
 * Use Yaml file to decide correctness of SV-COMP benchmarks.
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 */
public class SvcompTerminationTestResultDecider extends TerminationAnalysisTestResultDecider {

	/**
	 *
	 * @param ultimateRunDefinition
	 *
	 * @param unknownIsJUnitSuccess if true the TestResult UNKNOWN is a success for
	 *                              JUnit, if false, the TestResult UNKNOWN is a
	 *                              failure for JUnit.
	 */
	public SvcompTerminationTestResultDecider(final UltimateRunDefinition ultimateRunDefinition,
			final boolean unknownIsJUnitSuccess) {
		super(ultimateRunDefinition, unknownIsJUnitSuccess);
	}

	@Override
	public IExpectedResultFinder<TerminationAnalysisOverallResult> constructExpectedResultFinder() {
		final NestedMap2<String, String, TerminationAnalysisOverallResult> map = TestUtil
				.constructPropertyMapSvcompTermination(TestUtil.SVCOMP_PROP_TERMINATION);
		return new YamlBasedExpectedResultFinder<TerminationAnalysisOverallResult>(map);
	}

}
