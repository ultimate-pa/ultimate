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
package de.uni_freiburg.informatik.ultimatetest.suites.evals;

import java.util.Collection;
import de.uni_freiburg.informatik.ultimatetest.UltimateTestCase;

public class TACAS2015AlgoComparisonArray extends TACAS2015 {

	@Override
	public Collection<UltimateTestCase> createTestCases() {

		addTestCases("AutomizerCInline.xml", "TACASInterpolation2015/Automizer/Z3_Interpolation.epf", getPairs());
		addTestCases("AutomizerCInline.xml", "TACASInterpolation2015/Automizer/Princess_Interpolation.epf", getPairs());
//		addTestCases("AutomizerC.xml", "TACASInterpolation2015/Automizer/SMTInterpol_Interpolation.epf", getPairs());
//		addTestCases("AutomizerC.xml", "TACASInterpolation2015/Automizer/SMTInterpol_SP-IC-LV.epf", getPairs());
		addTestCases("AutomizerCInline.xml", "TACASInterpolation2015/Automizer/Z3_SP-IC-LV.epf", getPairs());
//		addTestCases("AutomizerC.xml", "TACASInterpolation2015/Automizer/CVC4_SP-IC-LV.epf", getPairs());
//		addTestCases("AutomizerC.xml", "TACASInterpolation2015/Automizer/SMTInterpol_SP-IC.epf", getPairs());
//		addTestCases("AutomizerC.xml", "TACASInterpolation2015/Automizer/Z3_SP-IC.epf", getPairs());
//		addTestCases("AutomizerC.xml", "TACASInterpolation2015/Automizer/CVC4_SP-IC.epf", getPairs());
//		addTestCases("AutomizerC.xml", "TACASInterpolation2015/Automizer/Z3_SP.epf", getPairs());
//		addTestCases("AutomizerC.xml", "TACASInterpolation2015/Automizer/Z3_SP-LV.epf", getPairs());

		// addTestCases("CodeCheckNoBE-C.xml",
		// "TACASInterpolation2015/Kojak-SP.epf", getPairs());
		// addTestCases("CodeCheckNoBE-C.xml",
		// "TACASInterpolation2015/Kojak-SP-IC.epf", getPairs());
		// addTestCases("CodeCheckNoBE-C.xml",
		// "TACASInterpolation2015/Kojak-SP-LV.epf", getPairs());
		// addTestCases("CodeCheckNoBE-C.xml",
		// "TACASInterpolation2015/Kojak-SP-IC-LV.epf", getPairs());
		// addTestCases("CodeCheckNoBE-C.xml",
		// "TACASInterpolation2015/Kojak-SMTInterpol.epf", getPairs());
		// addTestCases("CodeCheckNoBE-C.xml",
		// "TACASInterpolation2015/Kojak-Princess.epf", getPairs());
		return super.createTestCases();
	}

	@Override
	protected long getTimeout() {
		return 60 * 1000;
	}

	@Override
	protected String[] getDirectories() {
		// @formatter:off
		String[] directories = {
			"examples/programs/MapReduce/nondet/",
//		    "examples/svcomp/heap-manipulation",
//		    "examples/svcomp/list-properties",
//		    "examples/svcomp/ldv-regression",
//		    
//		    "examples/svcomp/loops",
//		    "examples/svcomp/loop-acceleration",
//		    "examples/svcomp/loop-invgen",
//		    "examples/svcomp/loop-lit",
//		    "examples/svcomp/loop-new",

		};
		return directories;
		// @formatter:on
	}

	@Override
	protected String[] getFileEndings() {
		return new String[] { ".c" };
	}
}
