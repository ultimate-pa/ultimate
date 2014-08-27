/**
 * 
 */
package de.uni_freiburg.informatik.ultimatetest.abstractinterpretation;

import java.io.File;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.Map.Entry;
import java.util.concurrent.TimeUnit;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.core.services.IResultService;
import de.uni_freiburg.informatik.ultimate.result.BenchmarkResult;
import de.uni_freiburg.informatik.ultimate.result.IResult;
import de.uni_freiburg.informatik.ultimate.util.Benchmark;
import de.uni_freiburg.informatik.ultimate.util.csv.ICsvProviderProvider;
import de.uni_freiburg.informatik.ultimatetest.decider.SafetyCheckTestResultDecider_OldVersion;
import de.uni_freiburg.informatik.ultimatetest.util.Util.ExpectedResult;

/**
 * @author Christopher Dillo
 *
 */
public class AbstractInterpretationTestResultDecider extends
		SafetyCheckTestResultDecider_OldVersion {
	
	public AbstractInterpretationTestResultDecider(File inputFile) {
		super(inputFile);
	}

	/** Peak memory in MiB **/
	private String m_resultMemory = "";
	/** Runtime in ms **/
	private String m_resultTime = "";

	@Override
	public TestResult getTestResult(IResultService resultService) {
		// get benchmark results
		Collection<IResult> results = new ArrayList<IResult>();
		for (Entry<String, List<IResult>> entry : resultService.getResults().entrySet()) {
			results.addAll(entry.getValue());
		}
		for (IResult r : results) {
			if (r instanceof BenchmarkResult) {
				BenchmarkResult<?> br = (BenchmarkResult<?>) r;
				ICsvProviderProvider<?> ic = br.getBenchmark();
				
				if (ic instanceof Benchmark) {
					Benchmark benchmark = (Benchmark) ic;
					
					long memory = 0; // in bytes
					double time = 0; // in milliseconds
					
					for (String title : benchmark.getTitles()) {
						long watchMem = benchmark.getStartHeapSize(title) + benchmark.getPeakMemoryConsumed(title);
						if (watchMem > memory)
							memory = watchMem;
						time += benchmark.getElapsedTime(title, TimeUnit.MILLISECONDS);
					}
					
					m_resultMemory = String.format("%d", (memory / 1024 / 1024)); // -> MiB
					m_resultTime = String.format("%.0f", time);
				}
			}
		}
		TestResult result = super.getTestResult(resultService);
		return result;
	}
	
	/**
	 * Message: Symbol for the LaTeX table denoting the expected result.
	 */
	protected void generateResultMessageAndCategory(SafetyCheckerResult safetyCheckerResult) {
		super.generateResultMessageAndCategory(safetyCheckerResult);
		
		// LaTeX prefix...
		setResultMessage(String.format("%s & %s & %s & %s \\\\ \n\t\t %% %s",
				expectedResultTag(getExpectedResult()),
				automizerResultTag(safetyCheckerResult.getAutomizerResultType()),
				m_resultTime, m_resultMemory, getResultMessage().replace("\n", " % % ")));
			// expected, actual result; runtime, max memory usage (original result message as comment)
		
		setResultCategory(automizerResultCategoryTag(safetyCheckerResult.getAutomizerResultType()));
	}


	@Override
	public boolean getJUnitTestResult(TestResult actualResult) {
		// Matthias wants to see Unknown results as success, and so does Christopher
		switch (actualResult) {
		case FAIL:
			return false;
		case SUCCESS:
		case UNKNOWN:
			return true;
		default:
			throw new IllegalArgumentException("actualResult has an unknown value");
		}
	}
	
	private String automizerResultCategoryTag(SafetyCheckerResultType result) {
		switch (result) {
		case SAFE :
			return "Safe";
		case UNKNOWN :
			return "Unknown";
		case UNSAFE :
			return "Unsafe";
		case SYNTAX_ERROR :
			return "Syntax error";
		case TIMEOUT :
			return "Timeout";
		case UNSUPPORTED_SYNTAX :
			return "Unsupported syntax";
		case EXCEPTION_OR_ERROR :
			return "Exception or error";
		case NO_RESULT :
			return "No result";
		default :
			return "---";
		}
	}
	
	private String automizerResultTag(SafetyCheckerResultType result) {
		switch (result) {
		case SAFE :
			return "$\\checkmark$";
		case UNKNOWN :
			return "?";
		case UNSAFE :
		case SYNTAX_ERROR :
		case TIMEOUT :
		case UNSUPPORTED_SYNTAX :
		case EXCEPTION_OR_ERROR :
			return "$\\times$";
		case NO_RESULT :
		default :
			return "---";
		}
	}
	
	private String expectedResultTag(ExpectedResult result) {
		switch (result) {
		case SAFE :
			return "$\\checkmark$";
		case UNSAFE :
		case SYNTAXERROR :
			return "$\\times$";
		case NOANNOTATION :
			return "?";
		default :
			return "--";
		}
	}

}
