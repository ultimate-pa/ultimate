/**
 * 
 */
package de.uni_freiburg.informatik.ultimatetest.suites.traceabstraction;

import java.util.Collection;

import de.uni_freiburg.informatik.ultimatetest.UltimateTestCase;

/**
 * Test for inlining with all SV-COMP from the Memsafety category.
 * @author heizmann@informatik.uni-freiburg.de
 */
public class InliningTest_Svcomp_Memsafety extends AbstractTraceAbstractionTestSuite {
	
	/** Limit the number of files per directory. */
	private static int m_FilesPerDirectoryLimit = Integer.MAX_VALUE;
	
	private static final DirectoryFileEndingsPair[] s_SVCOMP_Examples = {
//		/*** Category 7. Memory Safety ***/
		new DirectoryFileEndingsPair("examples/svcomp/memsafety/", new String[]{ ".i" }, m_FilesPerDirectoryLimit) ,
		new DirectoryFileEndingsPair("examples/svcomp/list-ext-properties/", new String[]{ ".i" }, m_FilesPerDirectoryLimit) ,
		new DirectoryFileEndingsPair("examples/svcomp/memory-alloca/", new String[]{ ".i" }, m_FilesPerDirectoryLimit) ,
		new DirectoryFileEndingsPair("examples/svcomp/memory-unsafe/", new String[]{ ".i" }, m_FilesPerDirectoryLimit) ,
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
			addTestCases("AutomizerCInline.xml", 
					"automizer/ForwardPredicates_SvcompMemsafety.epf", 
					s_SVCOMP_Examples);
			addTestCases("AutomizerCInlineWithBlockEncoding.xml", 
					"automizer/ForwardPredicates_SvcompMemsafetySeqbe.epf", 
					s_SVCOMP_Examples);
		}
		if (sAutomizerWithoutInlining) {
			addTestCases("AutomizerC.xml", 
					"automizer/ForwardPredicates_SvcompMemsafety.epf", 
					s_SVCOMP_Examples);
			addTestCases("AutomizerCWithBlockEncoding.xml", 
					"automizer/ForwardPredicates_SvcompMemsafetySeqbe.epf", 
					s_SVCOMP_Examples);
		}
		// return Util.firstN(super.createTestCases(), 3);
		return super.createTestCases();
	}

	
}
