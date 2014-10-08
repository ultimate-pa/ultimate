package de.uni_freiburg.informatik.ultimatetest.automatascript;

import java.io.File;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

import de.uni_freiburg.informatik.ultimatetest.UltimateRunDefinition;
import de.uni_freiburg.informatik.ultimatetest.UltimateStarter;
import de.uni_freiburg.informatik.ultimatetest.UltimateTestCase;
import de.uni_freiburg.informatik.ultimatetest.UltimateTestSuite;
import de.uni_freiburg.informatik.ultimatetest.summary.IIncrementalLog;
import de.uni_freiburg.informatik.ultimatetest.summary.ITestSummary;
import de.uni_freiburg.informatik.ultimatetest.util.Util;

public class AutomataScriptTestSuite extends UltimateTestSuite {

	private static final String m_Toolchain = "examples/toolchains/AutomataScriptInterpreter.xml";
	private static final File m_ToolchainFile = new File(Util.getPathFromTrunk(m_Toolchain));
	private static int m_Timeout = 10000;
	private static final String[] m_Directories = { "examples/Automata/atsTestFiles",
			"examples/Automata/AUTOMATA_SCRIPT", "examples/Automata/BuchiAutomata", "examples/Automata/BuchiNwa",
			"examples/Automata/finiteAutomata", "examples/Automata/nwa", "examples/Automata/nwaOperations",
	// the following two have still bugs
	// "examples/Automata/PetriNet",
	// "examples/Automata/senwa",
	// the following is not yet tested
	// "examples/Automata/syntaxError",
	};
	private static final String[] m_FileEndings = { ".ats" };

	@Override
	protected ITestSummary[] constructTestSummaries() {
		return new ITestSummary[] { new AutomataScriptTestSummary(this.getClass()) };
	}
	
	@Override
	protected IIncrementalLog[] constructIncrementalLog() {
		return new IIncrementalLog[0];
	}

	@Override
	public Collection<UltimateTestCase> createTestCases() {
		List<UltimateTestCase> testCases = new ArrayList<UltimateTestCase>();

		Collection<File> inputFiles = new ArrayList<File>();
		for (String directory : m_Directories) {
			inputFiles.addAll(getInputFiles(directory, m_FileEndings));
		}

		for (File inputFile : inputFiles) {
			File settingsFile = null;
			UltimateRunDefinition urd = new UltimateRunDefinition(inputFile, settingsFile, m_ToolchainFile);
			UltimateStarter starter = new UltimateStarter(urd, m_Timeout, null, null);
			UltimateTestCase utc = new UltimateTestCase(urd.generateShortStringRepresentation(),
					new AutomataScriptTestResultDecider(), starter,
					// m_Description + "_" + inputFile.getAbsolutePath(),
					urd, super.getSummaries(), null);
			testCases.add(utc);
		}
		return testCases;
	}

	private Collection<File> getInputFiles(String directory, String[] fileEndings) {
		return Util.getFiles(new File(Util.getPathFromTrunk(directory)), fileEndings);
	}

}
