package de.uni_freiburg.informatik.ultimatetest;

import static org.junit.Assert.fail;

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;

import org.apache.log4j.FileAppender;
import org.apache.log4j.PatternLayout;
import org.junit.After;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameters;

import de.uni_freiburg.informatik.ultimate.core.coreplugin.Application;
import de.uni_freiburg.informatik.ultimate.core.coreplugin.Application.Ultimate_Mode;
import de.uni_freiburg.informatik.ultimate.core.coreplugin.preferences.CorePreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceStore;
import de.uni_freiburg.informatik.ultimate.logging.UltimateLoggerFactory;

@RunWith(Parameterized.class)
public class UltimateTest {

	// just add to this method (for now)

	public static UltimateTestDescriptor[] getDescriptors() throws Exception {

		// return new UltimateTestDescriptor[] {
		// new UltimateTestDescriptor(
		// "F:\\repos\\ultimate fresher co\\trunk\\examples\\settings\\AutomizerSvcomp.settings",
		// "F:\\repos\\ultimate fresher co\\trunk\\examples\\toolchains\\TraceAbstractionCWithBlockEncoding.xml",
		// "F:\\repos\\svcomp\\ldv-challenges", new String[] { ".c", ".i" },
		// 5000),

		// new UltimateTestDescriptor(
		// getPathFromTrunk("examples\\settings\\AutomizerSvcomp.settings"),
		// getPathFromTrunk("examples\\toolchains\\TraceAbstractionCWithBlockEncoding.xml"),
		// getPathFromTrunk("examples\\programs\\minitests\\quantifier"),
		// new String[] { ".c", ".i" }, 5000)

		// new SVCOMP14TestDescriptor(
		// getPathFromTrunk("examples\\settings\\AutomizerSvcomp.settings"),
		// getPathFromTrunk("examples\\toolchains\\TraceAbstractionCWithBlockEncoding.xml"),
		// getPathFromTrunk("examples\\programs\\minitests\\quantifier\\todo"),
		// 5000, "Some"),

		// new SVCOMP14TestDescriptor(
		// getPathFromTrunk("examples\\settings\\AlexSVCOMPstandard"),
		// getPathFromTrunk("examples\\toolchains\\KojakC.xml"),
		// getPathFromTrunk("examples\\programs\\minitests"),
		// 5000, "Some")

		// new UltimateTestDescriptor(
		// getPathFromTrunk("examples\\settings\\AutomizerSvcomp.settings"),
		// getPathFromTrunk("examples\\toolchains\\TraceAbstractionCWithBlockEncoding.xml"),
		// getPathFromTrunk("..\\..\\svcomp"),
		// new String[] { ".c", ".i" }, 5000)

		// };

		/*
		 * SVCOMP 14 Categories: BitVectors Concurrency ControlFlowInteger
		 * DeviceDrivers64 DriverChallenges HeapManipulation Loops MemorySafety
		 * ProductLines Recursive Sequentialized Simple Stateful
		 */

		ArrayList<UltimateTestDescriptor> all = new ArrayList<UltimateTestDescriptor>();

		UltimateTestDescriptor[] alex = SVCOMP14TestDescriptor
				.createDescriptorsFromSVCOMPRootDirectory(
						getPathFromTrunk("../svcomp"),
						new HashMap<String, String>() {
							{
								put("MemorySafety",
										getPathFromTrunk("examples/settings/AlexSVCOMPmemsafety"));
								// put("Simple",
								// getPathFromTrunk("examples/settings/AlexSVCOMPstandard"));
								// put("ControlFlowInteger",
								// getPathFromTrunk("examples/settings/AlexSVCOMPstandard"));
							}
						}, getPathFromTrunk("examples/toolchains/KojakC.xml"),
						30000, "CodeCheck");

		UltimateTestDescriptor[] matthias = SVCOMP14TestDescriptor
				.createDescriptorsFromSVCOMPRootDirectory(
						getPathFromTrunk("../svcomp"),
						new HashMap<String, String>() {
							{
								put("MemorySafety",
										getPathFromTrunk("examples/settings/AutomizerSvcompSafety1Minute.bpl"));
								// put("Simple",
								// getPathFromTrunk("examples\\settings\\AutomizerSvcompSafety1Minute.bpl"));
								// put("ControlFlowInteger",
								// getPathFromTrunk("examples\\settings\\AutomizerSvcompSafety1Minute.bpl"));
							}
						},
						getPathFromTrunk("examples/toolchains/TraceAbstractionC.xml"),
						30000, "Automizer");

		all.addAll(Arrays.asList(alex));
		all.addAll(Arrays.asList(matthias));

		return all.toArray(new UltimateTestDescriptor[all.size()]);

	}

	// ignore everything below

	private static HashSet<TestSummary> sTestSummaries = new HashSet<TestSummary>();
	private UltimateTestDescriptor mDescriptor;
	private boolean mIsLast;

	public UltimateTest(UltimateTestDescriptor descriptor, boolean isLast) {
		mDescriptor = descriptor;
		mIsLast = isLast;
	}

	@Parameters
	public static Collection<Object[]> loadTestFiles() {

		ArrayList<Object[]> rtr = new ArrayList<Object[]>();
		UltimateTestDescriptor[] descriptors;
		try {
			descriptors = getDescriptors();
		} catch (Exception e) {
			e.printStackTrace();
			return null;
		}
		for (UltimateTestDescriptor descriptor : descriptors) {
			Collection<File> files = descriptor.getFiles();

			for (File f : files) {
				rtr.add(new Object[] { descriptor.copy(f.getAbsolutePath()),
						false });
			}
		}
		rtr.get(rtr.size() - 1)[1] = true;
		return rtr;
	}

	private static String getPathFromTrunk(String path) {
		File trunk = new File(System.getProperty("user.dir")).getParentFile()
				.getParentFile();
		File relative = new File(trunk.getAbsolutePath() + File.separator
				+ path);
		return relative.getAbsolutePath();
	}

	private static String getPathFromHere(String path) {
		File here = new File(System.getProperty("user.dir"));
		File relative = new File(here.getAbsolutePath() + File.separator + path);
		return relative.getAbsolutePath();
	}

	private static String getPathFromSurefire(String path) {
		File trunk = new File(System.getProperty("user.dir"));
		File relative = new File(trunk.getAbsolutePath() + File.separator
				+ "target" + File.separator + "surefire-reports"
				+ File.separator + UltimateTest.class.getCanonicalName()
				+ File.separator + path);
		


		return relative.getAbsolutePath();
	}

	@Test
	public void testSingleFile() {
		Application ultimate = new Application(Ultimate_Mode.EXTERNAL_EXECUTION);
		ultimate.setM_InputFile(mDescriptor.getPathInputFile());
		ultimate.setDeadline(mDescriptor.getDeadline());
		ultimate.setSettingsFile(mDescriptor.getPathSettings());
		ultimate.setToolchainXML(mDescriptor.getPathToolchain());

		FileAppender appender = null;
		String logfilepath = mDescriptor.generateLogFilename();
		try {
			appender = new FileAppender(
					new PatternLayout(
							new UltimatePreferenceStore(ultimate.getPluginID())
									.getString(CorePreferenceInitializer.LABEL_LOG4J_PATTERN)),
					logfilepath);
			UltimateLoggerFactory.getInstance().addAppender(appender);
		} catch (IOException e1) {
			e1.printStackTrace();
			completeSingleTest(appender, logfilepath);
			fail("Could not create log file");
		}

		try {
			ultimate.start(null);
			boolean fail = mDescriptor.testFailed();
			completeSingleTest(appender, logfilepath);
			if (fail) {
				fail();
			}
		} catch (Exception e) {
			e.printStackTrace();
			completeSingleTest(appender, logfilepath);
			fail("Ultimate should run without exception");
		}
	}

	public void completeSingleTest(FileAppender appender, String logPath) {
		UltimateLoggerFactory.getInstance().removeAppender(appender);
		System.out.println("[[ATTACHMENT|" + logPath + "]]");
	}

	@After
	public void writeSummary() {
		sTestSummaries.add(mDescriptor.getSummary());

		if (!mIsLast) {
			return;
		}

		System.out.println("Writing " + sTestSummaries.size() + " summaries");
		for (TestSummary summary : sTestSummaries) {
			File logFile = new File(getPathFromSurefire(summary
					.getSummaryLogFile().getName()));

			if(!logFile.isDirectory()){
				logFile.getParentFile().mkdirs();
			}
			
			String summaryLog = summary.getSummaryLog();
			if (summaryLog == null || summaryLog.isEmpty()) {
				return;
			}

			try {
				FileWriter fw = new FileWriter(logFile);
				System.out.println("Writing test summary log for " + summary
						+ " to " + logFile);
				fw.write(summaryLog);
				fw.close();
			} catch (IOException e) {
				e.printStackTrace();
			}
		}

	}

}
