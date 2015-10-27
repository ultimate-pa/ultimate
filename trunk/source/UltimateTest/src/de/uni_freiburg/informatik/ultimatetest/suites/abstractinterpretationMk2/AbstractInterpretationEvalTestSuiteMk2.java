/**
 * 
 */
package de.uni_freiburg.informatik.ultimatetest.suites.abstractinterpretationMk2;

import java.util.ArrayList;
import java.util.Collection;

import de.uni_freiburg.informatik.ultimatetest.UltimateTestCase;
import de.uni_freiburg.informatik.ultimatetest.reporting.ITestSummary;
import de.uni_freiburg.informatik.ultimatetest.summaries.AbstractInterpretationMk2ComparisonTestSummary;
import de.uni_freiburg.informatik.ultimatetest.summaries.AbstractInterpretationMk2LaTeXTestSummary;
import de.uni_freiburg.informatik.ultimatetest.summaries.AbstractInterpretationTestSummary;

/**
 * Stolen from Svcomp_Reach_PreciseMemoryModel ;-)
 */
public class AbstractInterpretationEvalTestSuiteMk2 extends
		AbstractAbstractInterpretationMk2TestSuite
{
	private static boolean m_compareToAutomizer = true;
	private static boolean m_compareDomains = true;
	private static boolean m_compareCompound = true;

	@Override
	protected ITestSummary[] constructTestSummaries()
	{
		ArrayList<ITestSummary> tests = new ArrayList<ITestSummary>();

		tests.add(new AbstractInterpretationTestSummary(this.getClass()));
		tests.add(new AbstractInterpretationMk2LaTeXTestSummary(this.getClass()));
		
		if (m_compareDomains)
		{
			tests.add(new AbstractInterpretationMk2ComparisonTestSummary(this.getClass(),
					"AI2_INT", "AI2_PLT", "Interval Domain", "Polyhedron Domain"));
		}

		if (m_compareToAutomizer)
		{
			tests.add(new AbstractInterpretationMk2ComparisonTestSummary(this.getClass(),
					"AI2_PLT", "automizer", "Polyhedron Domain", "Trace Abstraction"));

		}

		if (m_compareToAutomizer)
		{
			tests.add(new AbstractInterpretationMk2ComparisonTestSummary(this.getClass(),
					"AI2_INT", "AI2_CMP", "Interval Domain", "Compound Domain"));

		}
		return tests.toArray(new ITestSummary[tests.size()]);  
	}

	private static final String[] m_directories = {
//		"examples/programs/abstractInterpretation/",
		//"examples/programs/abstractInterpretationNoRec/",
			/* ULTIMATE repo */
			// "examples/programs/regression/bpl/",
			// "examples/programs/regression/c/",
			// "examples/programs/recursivePrograms",
			/* SV-COMP repo */
//			 "examples/svcomp/loops/", // SPLIT
			// "examples/svcomp/loopsSelection/",
			// "examples/svcomp/eca/", // SPLIT
			// "examples/svcomp/ecaSelection/",
			// "examples/svcomp/systemc/", // SPLIT
			// "examples/svcomp/systemc1/",
			// "examples/svcomp/systemc2/",
		
		"examples/svcomp/loops/eureka_01_false-unreach-call.c"
		
	};

	// Time out for each test case in milliseconds
	private static int m_Timeout = 30000;

	@Override
	public Collection<UltimateTestCase> createTestCases()
	{
		if (m_compareDomains)
		{
			// Abstract Interpretation INTERVAL
			addTestCases(
					"AbstractInterpretationMk2.xml",
					"ai/AI2_INT.epf",
					m_directories,
					new String[] { ".bpl" },
					"AI .bpl",
					"AI2_INTbpl",
					m_Timeout);
			addTestCases(
					"AbstractInterpretationMk2C.xml",
					"ai/AI2_INT.epf",
					m_directories,
					new String[] { ".c" },
					"AI .c",
					"AI2_INTc",
					m_Timeout);
			// Abstract Interpretation POLYTOPE
		}
		addTestCases(
				"AbstractInterpretationMk2.xml",
				"ai/AI2_PLT.epf",
				m_directories,
				new String[] { ".bpl" },
				"AI .bpl",
				"AI2_PLTbpl",
				m_Timeout);
		addTestCases(
				"AbstractInterpretationMk2C.xml",
				"ai/AI2_PLT.epf",
				m_directories,
				new String[] { ".c" },
				"AI .c",
				"AI2_PLTc",
				m_Timeout);

		if (m_compareCompound)
		{
			// Abstract Interpretation INTERVAL
			addTestCases(
					"AbstractInterpretationMk2.xml",
					"ai/AI2_CMP.epf",
					m_directories,
					new String[] { ".bpl" },
					"AI .bpl",
					"AI2_CMPbpl",
					m_Timeout);
			addTestCases(
					"AbstractInterpretationMk2C.xml",
					"ai/AI2_CMP.epf",
					m_directories,
					new String[] { ".c" },
					"AI .c",
					"AI2_CMPc",
					m_Timeout);
			// Abstract Interpretation POLYTOPE
		}
 
		if (m_compareToAutomizer)
		{
			addTestCases(
					"AutomizerBpl.xml",
					"ai/AI.epf",
					// "ai/AI2.epf",
					m_directories,
					new String[] { ".bpl" },
					"AI.bpl",
					"automizerbpl",
					m_Timeout);
			addTestCases(
					"AutomizerC.xml",
					"ai/Automizer.epf",
					// "ai/AI2.epf",
					m_directories,
					new String[] { ".c" },
					"AI.c",
					"automizerc",
					m_Timeout);
		}
		// return Util.firstN(super.createTestCases(), 20);
		return super.createTestCases();
	}
}
