/*
 * Copyright (C) 2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
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
package de.uni_freiburg.informatik.ultimatetest.suites.abstractinterpretation;

import java.util.Collection;

import de.uni_freiburg.informatik.ultimatetest.UltimateTestCase;

/**
 * Stolen from Svcomp_Reach_PreciseMemoryModel ;-)
 */
public class AbstractInterpretationEvalTestSuite extends AbstractAbstractInterpretationTestSuite {

	private boolean mCompareToAutomizer = !false;

	private static final String[] m_directories = {
			/* ULTIMATE repo */
			"examples/programs/regression/bpl/", 
			"examples/programs/regression/c/",
			"examples/programs/recursivePrograms",
			
			/* SV-COMP repo */
			// "examples/svcomp/loops/", // SPLIT
			// "examples/svcomp/loopsSelection/",
			// "examples/svcomp/eca/", // SPLIT
			// "examples/svcomp/ecaSelection/",
			// "examples/svcomp/systemc/", // SPLIT
			// "examples/svcomp/systemc1/",
			// "examples/svcomp/systemc2/",
	};

	// Time out for each test case in milliseconds
	private static int m_Timeout = 20000;

	@Override
	public Collection<UltimateTestCase> createTestCases() {
		// Abstract Interpretation
		addTestCases("AbstractInterpretation.xml", "ai/AI.epf", m_directories, new String[] { ".bpl" }, "AI .bpl",
				"abstractinterpretationbpl", m_Timeout);
		addTestCases("AbstractInterpretationC.xml", "ai/AI.epf", m_directories, new String[] { ".c" }, "AI .c",
				"abstractinterpretationc", m_Timeout);
		// Automizer
		if (mCompareToAutomizer) {
			addTestCases("AutomizerBpl.xml", "ai/AI.epf", m_directories, new String[] { ".bpl" }, "AI .bpl",
					"automizerbpl", m_Timeout);
			addTestCases("AutomizerC.xml", "ai/AI.epf", m_directories, new String[] { ".c" }, "AI .c", "automizerc",
					m_Timeout);
		}
		// return Util.firstN(super.createTestCases(), 20);
		return super.createTestCases();
	}
}
