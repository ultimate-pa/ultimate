/**
 * 
 */
package de.uni_freiburg.informatik.ultimatetest.traceabstraction;

import java.util.Arrays;
import java.util.Collection;
import java.util.List;

import de.uni_freiburg.informatik.ultimatetest.UltimateTestCase;
import de.uni_freiburg.informatik.ultimatetest.summary.DefaultIncrementalLogfile;
import de.uni_freiburg.informatik.ultimatetest.summary.IIncrementalLog;

/**
 * @author heizmann@informatik.uni-freiburg.de
 * 
 */
public class Svcomp_Reach_PreciseMemoryModel extends AbstractTraceAbstractionTestSuite {
	private static final String[] m_Directories = {
	// "examples/svcomp/bitvector/",
	// "examples/svcomp/bitvector-regression/",
	// "examples/svcomp/ntdrivers-simplified/",
	// "examples/svcomp/ssh-simplified/",
	// "examples/svcomp/locks/",
	// "examples/svcomp/eca/",
	// "examples/svcomp/loops/",
	// "examples/svcomp/product-lines/",
	// "examples/svcomp/heap-manipulation/",
	// "examples/svcomp/list-properties/",
	// "examples/svcomp/ldv-regression/",
	// "examples/svcomp/ddv-machzwd/",
	// "examples/svcomp/recursive/",
	"examples/svcomp/systemc/",
	// "examples/svcomp/seq-mthreaded/",
	// "examples/svcomp/seq-pthread/"
	};

	// Time out for each test case in milliseconds
	private static int m_Timeout = 20000;

	private static final boolean m_AutomizerWithForwardPredicates = true;
	private static final boolean m_AutomizerWithBackwardPredicates = true;

	private List<IIncrementalLog> mLogFiles;

	public Svcomp_Reach_PreciseMemoryModel() {
		mLogFiles = Arrays.asList(new IIncrementalLog[] { new DefaultIncrementalLogfile(getClass()) });
	}
	
	@Override
	public Collection<UltimateTestCase> createTestCases() {
		if (m_AutomizerWithForwardPredicates) {
			addTestCases("AutomizerC.xml", "automizer/ForwardPredicates_SvcompReachPreciseMM.epf", m_Directories,
					new String[] { ".c", ".i" },
					// "Trace Abstraction via Forward Predicates (SP)",
					// "CFilesForwardPredicates",
					m_Timeout);
		}
		if (m_AutomizerWithBackwardPredicates) {
			addTestCases("AutomizerC.xml", "automizer/BackwardPredicates_SvcompReachPreciseMM.epf", m_Directories,
					new String[] { ".c", ".i" },
					// "Trace Abstraction via Backward Predicates (BP)",
					// "CFilesBackwardPredicates",
					m_Timeout);
		}
		// return Util.firstN(super.createTestCases(), 3);
		return super.createTestCases();
	}

	@Override
	public List<IIncrementalLog> getLogFiles() {
		return mLogFiles;
	}
}
