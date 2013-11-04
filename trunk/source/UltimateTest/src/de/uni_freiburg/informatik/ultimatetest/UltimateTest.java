package de.uni_freiburg.informatik.ultimatetest;

import static org.junit.Assert.*;

import java.io.File;
import java.io.IOException;
import java.text.DateFormat;
import java.text.SimpleDateFormat;
import java.util.ArrayList;
import java.util.Calendar;
import java.util.Collection;
import java.util.List;
import java.util.Map.Entry;

import org.apache.log4j.FileAppender;
import org.apache.log4j.Logger;
import org.apache.log4j.PatternLayout;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameters;

import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.core.coreplugin.Application;
import de.uni_freiburg.informatik.ultimate.core.coreplugin.Application.Ultimate_Mode;
import de.uni_freiburg.informatik.ultimate.core.coreplugin.preferences.CorePreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceStore;
import de.uni_freiburg.informatik.ultimate.logging.UltimateLoggerFactory;
import de.uni_freiburg.informatik.ultimate.result.IResult;
import de.uni_freiburg.informatik.ultimate.result.NoResult;
import de.uni_freiburg.informatik.ultimate.result.SyntaxErrorResult;
import de.uni_freiburg.informatik.ultimate.result.TimeoutResult;

@RunWith(Parameterized.class)
public class UltimateTest {

	// just add to this method (for now)

	public static UltimateTestDescriptor[] getDescriptors() {
		return new UltimateTestDescriptor[] { new UltimateTestDescriptor(
				"F:\\repos\\ultimate fresher co\\trunk\\examples\\settings\\AutomizerSvcomp.settings",
				"F:\\repos\\ultimate fresher co\\trunk\\examples\\toolchains\\TraceAbstractionCWithBlockEncoding.xml",
				"F:\\repos\\svcomp\\ldv-challenges", ".c", 5000) };
	}

	// ignore everything below

	private UltimateTestDescriptor mDescriptor;

	public UltimateTest(UltimateTestDescriptor descriptor) {
		mDescriptor = descriptor;
	}

	@Parameters(name = "{index} : {0}")
	public static Collection<Object[]> loadTestFiles() {
		ArrayList<Object[]> rtr = new ArrayList<Object[]>();
		UltimateTestDescriptor[] descriptors = getDescriptors();

		for (UltimateTestDescriptor descriptor : descriptors) {
			Collection<File> files = walk(descriptor.getPathInputFile(),
					descriptor.getFileEnding());
			for (File f : files) {
				rtr.add(new Object[] { descriptor.copy(f.getAbsolutePath()) });
			}
		}
		return rtr;
	}

	private static Collection<File> walk(File root, String endings) {
		ArrayList<File> rtr = new ArrayList<File>();
		File[] list = root.listFiles();

		if (list == null) {
			return rtr;
		}

		for (File f : list) {
			if (f.isDirectory()) {
				rtr.addAll(walk(f, endings));
			} else {
				if (endings == null || f.getAbsolutePath().endsWith(endings)) {
					rtr.add(f);
				}
			}
		}
		return rtr;
	}

	@Test
	public void testSingleFile() {

		Application ultimate = new Application(Ultimate_Mode.EXTERNAL_EXECUTION);
		ultimate.setM_InputFile(mDescriptor.getPathInputFile());
		ultimate.setDeadline(mDescriptor.getDeadline());
		ultimate.setSettingsFile(mDescriptor.getPathSettings());
		ultimate.setToolchainXML(mDescriptor.getPathToolchain());

		FileAppender appender = null;
		try {
			appender = new FileAppender(
					new PatternLayout(
							new UltimatePreferenceStore(ultimate.getPluginID())
									.getString(CorePreferenceInitializer.LABEL_LOG4J_PATTERN)),
					generateLogFilename());
			UltimateLoggerFactory.getInstance().addAppender(appender);
		} catch (IOException e1) {
			e1.printStackTrace();
			fail("Could not create log file");
		}

		try {
			ultimate.start(null);
			UltimateLoggerFactory.getInstance().removeAppender(appender);
			if (testFailed()) {
				fail();
			}

		} catch (Exception e) {
			e.printStackTrace();
			fail("Ultimate should run without exception");
		}


	}

	public String generateLogFilename() {

		DateFormat dateFormat = new SimpleDateFormat("yyyy-MM-dd-HH-mm-ss");

		String s = mDescriptor.getPathInputFile().getParent()
				+ File.separator
				+ "UltimateTest "
				+ dateFormat.format(Calendar.getInstance().getTime())
				+ " "
				+ mDescriptor.getPathInputFile().getName()
						.replaceAll(mDescriptor.getFileEnding(), "") + ".log";
		s = s.replaceAll(" ", "_");
		return s;
	}

	public boolean testFailed() {
		Logger log = UltimateLoggerFactory.getInstance().getLoggerById(
				"UltimateTest");
		log.debug("========== TEST RESULTS ==========");
		log.debug("Results for " + mDescriptor.getPathInputFile());
		boolean fail = false;
		for (Entry<String, List<IResult>> entry : UltimateServices
				.getInstance().getResultMap().entrySet()) {
			int i = 0;
			for (IResult result : entry.getValue()) {
				log.debug("[" + i + "] " + entry.getKey() + " --> ["
						+ result.getClass().getSimpleName() + "] "
						// + result.getLocation().toString() + " "
						+ result.getLongDescription());
				++i;
				if (result instanceof SyntaxErrorResult
						|| result instanceof TimeoutResult
						|| result instanceof NoResult) {
					fail = true;
				}
			}
		}
		
		log.debug("========== END ==========");
		return fail;
	}

}
