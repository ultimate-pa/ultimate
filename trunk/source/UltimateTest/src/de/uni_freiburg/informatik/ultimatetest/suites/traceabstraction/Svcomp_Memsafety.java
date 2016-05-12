/*
 * Copyright (C) 2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE Test Library.
 * 
 * The ULTIMATE Test Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE Test Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Test Library. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Test Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE Test Library grant you additional permission 
 * to convey the resulting work.
 */
/**
 * 
 */
package de.uni_freiburg.informatik.ultimatetest.suites.traceabstraction;

import java.util.Collection;

import de.uni_freiburg.informatik.ultimate.test.UltimateTestCase;

/**
 * @author heizmann@informatik.uni-freiburg.de
 *
 */
public class Svcomp_Memsafety extends
		AbstractTraceAbstractionTestSuite {
	private static final String[] m_Directories = { 
		"examples/svcomp/memsafety",
		"examples/svcomp/memsafety-ext",
		"examples/svcomp/list-ext-properties",
		"examples/svcomp/memory-alloca/"
		};
	
	/**
	 * {@inheritDoc}
	 */
	@Override
	public long getTimeout() {
		return 60 * 1000;
	}

	private static final boolean m_AutomizerWithForwardPredicates = true;
	private static final boolean m_AutomizerWithBackwardPredicates = !true;
	
	@Override
	public Collection<UltimateTestCase> createTestCases() {
		if (m_AutomizerWithForwardPredicates) {
			addTestCase(
					"AutomizerC.xml",
					"automizer/ForwardPredicates_SvcompMemsafety.epf",
				    m_Directories,
				    new String[] {".i"});
		}
		if (m_AutomizerWithForwardPredicates) {
			addTestCase(
					"AutomizerC.xml",
					"automizer/ForwardPredicates_SvcompMemsafetyConservative.epf",
				    m_Directories,
				    new String[] {".i"});
		}
//		if (m_AutomizerWithForwardPredicates) {
//			addTestCases(
//					"AutomizerC.xml",
//					"automizer/ForwardPredicates_SvcompMemsafetyLbe.epf",
//				    m_Directories,
//				    new String[] {".i"},
//				    m_Timeout);
//		}
//		if (m_AutomizerWithForwardPredicates) {
//			addTestCases(
//					"AutomizerC.xml",
//					"automizer/ForwardPredicates_SvcompMemsafetyLbeConservative.epf",
//				    m_Directories,
//				    new String[] {".i"},
//				    m_Timeout);
//		}
		if (m_AutomizerWithForwardPredicates) {
			addTestCase(
					"AutomizerCWithBlockEncoding.xml",
					"automizer/ForwardPredicates_SvcompMemsafetySeqbe.epf",
				    m_Directories,
				    new String[] {".i"});
		}
		if (m_AutomizerWithForwardPredicates) {
			addTestCase(
					"AutomizerCWithBlockEncoding.xml",
					"automizer/ForwardPredicates_SvcompMemsafetySeqbeConservative.epf",
				    m_Directories,
				    new String[] {".i"});
		}
//		if (m_AutomizerWithForwardPredicates) {
//			addTestCases(
//					"AutomizerC.xml",
//					"automizer/ForwardPredicates_SvcompMemsafetyAdditionalAssume.epf",
//				    m_Directories,
//				    new String[] {".i"},
//				    m_Timeout);
//		}
		if (m_AutomizerWithBackwardPredicates) {
			addTestCase(
					"AutomizerC.xml",
					"automizer/BackwardPredicates_SvcompMemsafety.epf",
				    m_Directories,
				    new String[] {".c", ".i"});
		}
		return super.createTestCases();
	}
}
