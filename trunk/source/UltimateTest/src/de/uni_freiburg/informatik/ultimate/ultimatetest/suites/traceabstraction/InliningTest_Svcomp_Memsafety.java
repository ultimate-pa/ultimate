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

import de.uni_freiburg.informatik.ultimate.test.DirectoryFileEndingsPair;
import de.uni_freiburg.informatik.ultimate.test.UltimateTestCase;

/**
 * Test for inlining with all SV-COMP from the Memsafety category.
 * @author heizmann@informatik.uni-freiburg.de
 */
public class InliningTest_Svcomp_Memsafety extends AbstractTraceAbstractionTestSuite {
	
	/** Limit the number of files per directory. */
	private static int mFilesPerDirectoryLimit = Integer.MAX_VALUE;
	
	private static final DirectoryFileEndingsPair[] s_SVCOMP_Examples = {
//		/*** Category 7. Memory Safety ***/
		new DirectoryFileEndingsPair("examples/svcomp/memsafety/", new String[]{ ".i" }, mFilesPerDirectoryLimit) ,
		new DirectoryFileEndingsPair("examples/svcomp/list-ext-properties/", new String[]{ ".i" }, mFilesPerDirectoryLimit) ,
		new DirectoryFileEndingsPair("examples/svcomp/memory-alloca/", new String[]{ ".i" }, mFilesPerDirectoryLimit) ,
		new DirectoryFileEndingsPair("examples/svcomp/memory-unsafe/", new String[]{ ".i" }, mFilesPerDirectoryLimit) ,
	};

	@Override
	public long getTimeout() {
		return 60 * 1000;
	}

	private static final boolean sAutomizerWithInlining = true;
	private static final boolean sAutomizerWithoutInlining = true;
	
	@Override
	public Collection<UltimateTestCase> createTestCases() {
		if (sAutomizerWithInlining) {
			addTestCase("AutomizerCInline.xml", 
					"automizer/ForwardPredicates_SvcompMemsafety.epf", 
					s_SVCOMP_Examples);
			addTestCase("AutomizerCInlineWithBlockEncoding.xml", 
					"automizer/ForwardPredicates_SvcompMemsafetySeqbe.epf", 
					s_SVCOMP_Examples);
		}
		if (sAutomizerWithoutInlining) {
			addTestCase("AutomizerC.xml", 
					"automizer/ForwardPredicates_SvcompMemsafety.epf", 
					s_SVCOMP_Examples);
			addTestCase("AutomizerCWithBlockEncoding.xml", 
					"automizer/ForwardPredicates_SvcompMemsafetySeqbe.epf", 
					s_SVCOMP_Examples);
		}
		// return Util.firstN(super.createTestCases(), 3);
		return super.createTestCases();
	}

	
}
