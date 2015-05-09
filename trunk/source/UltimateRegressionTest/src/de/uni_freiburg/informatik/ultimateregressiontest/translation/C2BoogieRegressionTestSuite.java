package de.uni_freiburg.informatik.ultimateregressiontest.translation;

import java.io.File;
import java.util.Collection;

import org.junit.AfterClass;

import de.uni_freiburg.informatik.ultimateregressiontest.AbstractRegressionTestSuite;
import de.uni_freiburg.informatik.ultimatetest.UltimateRunDefinition;
import de.uni_freiburg.informatik.ultimatetest.decider.ITestResultDecider;
import de.uni_freiburg.informatik.ultimatetest.decider.TranslationTestResultDecider;
import de.uni_freiburg.informatik.ultimatetest.util.Util;

/**
 * This testsuite tests whether the CACSL2BoogieTranslator translates C programs
 * to correct Boogie code. It runs CACSL2BoogieTranslator and BoogiePrinter on C
 * programs and compares the resulting Boogie file with a reference file.
 * 
 * The result of this test and of the comparison is decided in
 * {@link TranslationTestResultDecider}.
 * 
 * @author dietsch@informatik.uni-freiburg.de
 * 
 */
public class C2BoogieRegressionTestSuite extends AbstractRegressionTestSuite {

	private static String sRootFolder = Util.getPathFromTrunk("examples/CToBoogieTranslation");
	
	private static final long DEFAULT_TIMEOUT_MILLIS = 5000;
	private static final String TEMPORARY_BOOGIE_FILENAME_PATTERN = ".*regression.*BoogiePrinter_.*UID.*";

	/**
	 * Default constructor that will be called by the Ultimate test framework.
	 */
	public C2BoogieRegressionTestSuite() {
		super();
		mTimeout = DEFAULT_TIMEOUT_MILLIS;
		mRootFolder = sRootFolder;
		mFiletypesToConsider = new String[] { ".c" };
	}

	@Override
	protected ITestResultDecider getTestResultDecider(UltimateRunDefinition runDefinition) {
		return new TranslationTestResultDecider(runDefinition.getInput().getAbsolutePath());
	}

	/**
	 * Deletes the temporary Boogie files that have been created after the
	 * execution of this testsuite. Will be called by the JUnit framework.
	 */
	@AfterClass
	public static void cleanupBoogiePrinterFiles() {

		final File root = getRootFolder(sRootFolder);

		Collection<File> files = Util.getFiles(root, new String[] { ".bpl" });
		files = Util.filterFiles(files, TEMPORARY_BOOGIE_FILENAME_PATTERN);

		if (files.isEmpty()) {
			sLogger.info(String.format("No cleanup of %s necessary, no files matching the pattern %s have been found",
					sRootFolder, TEMPORARY_BOOGIE_FILENAME_PATTERN));
			return;
		}

		sLogger.info(String.format("Begin cleanup of %s", sRootFolder));
		for (final File f : files) {
			try {
				if (f.delete()) {
					sLogger.info(String.format("Sucessfully deleted %s", f.getAbsolutePath()));
				} else {
					sLogger.info(String.format("Deleteing %s failed", f.getAbsolutePath()));
				}
			} catch (SecurityException e) {
				sLogger.error(e);
			}
		}
	}
}
