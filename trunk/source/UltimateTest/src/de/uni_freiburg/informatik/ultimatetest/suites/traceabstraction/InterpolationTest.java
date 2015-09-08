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

import de.uni_freiburg.informatik.ultimatetest.UltimateTestCase;

/**
 * @author heizmann@informatik.uni-freiburg.de
 *
 */
public class InterpolationTest extends
		AbstractTraceAbstractionTestSuite {
	private static final String[] m_Directories = {
		"examples/programs/regression/",
		"examples/programs/quantifier/",
		"examples/programs/recursivePrograms",
		"examples/programs/toy",
//		"examples/termination/AProVE"
//		"examples/svcomp/recursive/",
//		"examples/svcomp/ssh-simplified/",
//		"examples/svcomp/memsafety",
//		"examples/svcomp/memsafety-ext",
//		"examples/svcomp/list-ext-properties",
//		"examples/svcomp/memory-alloca",
//		"examples/svcomp/ssh",
//		"examples/svcomp/ldv-regression",
//		"examples/programs/nonlinearArithmetic/reach",
	};
	
	
	/**
	 * {@inheritDoc}
	 */
	@Override
	public long getTimeout() {
		return 10 * 1000;
	}

	private static final boolean s_ForwardPredicates = true;
	private static final boolean s_SMTInterpol = !true;
	private static final boolean s_iZ3 = !true;
	private static final boolean s_Princess = !true;
	private static final boolean s_CVC4 = true;
	
	
	@Override
	public Collection<UltimateTestCase> createTestCases() {
		if (s_ForwardPredicates) {
			addTestCases(
					"AutomizerBpl.xml",
					"automizer/interpolation/ForwardPredicates.epf",
				    m_Directories,
				    new String[] {".bpl"});
			addTestCases(
					"AutomizerC.xml",
					"automizer/interpolation/ForwardPredicates.epf",
				    m_Directories,
				    new String[] {".i", ".c"});
		}
		if (s_SMTInterpol) {
			addTestCases(
					"AutomizerBpl.xml",
					"automizer/interpolation/SMTInterpol.epf",
				    m_Directories,
				    new String[] {".bpl"});
			addTestCases(
					"AutomizerC.xml",
					"automizer/interpolation/SMTInterpol.epf",
				    m_Directories,
				    new String[] {".c", ".i"});
		} 
		if (s_iZ3) {
			addTestCases(
					"AutomizerBpl.xml",
					"automizer/interpolation/iZ3.epf",
				    m_Directories,
				    new String[] {".bpl"});
			addTestCases(
					"AutomizerC.xml",
					"automizer/interpolation/iZ3.epf",
				    m_Directories,
				    new String[] {".c", ".i"});
		}
		if (s_Princess) {
			addTestCases(
					"AutomizerBpl.xml",
					"automizer/interpolation/Princess.epf",
				    m_Directories,
				    new String[] {".bpl"});
			addTestCases(
					"AutomizerC.xml",
					"automizer/interpolation/Princess.epf",
				    m_Directories,
				    new String[] {".i", ".c"});
		}
		if (s_CVC4) {
			addTestCases(
					"AutomizerBpl.xml",
					"automizer/interpolation/CVC4ForwardPredicates.epf",
				    m_Directories,
				    new String[] {".bpl"});
			addTestCases(
					"AutomizerC.xml",
					"automizer/interpolation/CVC4ForwardPredicates.epf",
				    m_Directories,
				    new String[] {".i", ".c"});
		}
		return super.createTestCases();
	}
}
