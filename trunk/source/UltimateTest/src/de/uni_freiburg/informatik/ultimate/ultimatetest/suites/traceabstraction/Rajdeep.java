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
package de.uni_freiburg.informatik.ultimate.ultimatetest.suites.traceabstraction;

import java.util.Collection;

import de.uni_freiburg.informatik.ultimate.test.UltimateTestCase;

/**
 * @author heizmann@informatik.uni-freiburg.de
 * 
 */
public class Rajdeep extends AbstractTraceAbstractionTestSuite {

	/** Limit the number of files per directory. */
//	private static int mFilesPerDirectoryLimit = Integer.MAX_VALUE;
	

	
	private static final String[] mInputFiles = {
			"examples/programs/real-life/RajdeepMukherjee/"
		};
	
	/**
	 * {@inheritDoc}
	 */
	@Override
	public long getTimeout() {
		return 180 * 1000;
	}

	private static final String[] mSettings = {
//		"svcomp2016/svcomp-Reach-32bit-Automizer_Default.epf",
//		"svcomp2016/svcomp-Reach-32bit-Automizer_Bitvector.epf",
		"automizer/interpolation/bitvector/Reach-32bit-Z3-IcSpLv-Bitvector.epf",
//		"automizer/interpolation/bitvector/Reach-32bit-Z3-IcWpLv-Bitvector.epf",
//		"automizer/interpolation/bitvector/Reach-32bit-CVC4-IcSpLv-Bitvector.epf",
//		"automizer/interpolation/bitvector/Reach-32bit-CVC4-IcWpLv-Bitvector.epf",
	};
	
	private static final String[] mCToolchains = {
//		"AutomizerC.xml",
		"AutomizerCInline.xml",
	};
	
	
	

	@Override
	public Collection<UltimateTestCase> createTestCases() {
		for (final String setting : mSettings) {
			for (final String toolchain : mCToolchains) {
				addTestCase(toolchain, setting, mInputFiles, new String[] {".c", ".i"});
			}
		}
		return super.createTestCases();
	}

	
}
