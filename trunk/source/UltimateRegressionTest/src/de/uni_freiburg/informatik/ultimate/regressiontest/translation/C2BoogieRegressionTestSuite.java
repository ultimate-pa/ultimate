/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE Regression Test Library.
 * 
 * The ULTIMATE Regression Test Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE Regression Test Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Regression Test Library. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Regression Test Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE Regression Test Library grant you additional permission 
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.regressiontest.translation;

import java.io.File;
import java.util.Collection;

import org.junit.AfterClass;

import de.uni_freiburg.informatik.ultimate.regressiontest.AbstractRegressionTestSuite;
import de.uni_freiburg.informatik.ultimate.test.UltimateRunDefinition;
import de.uni_freiburg.informatik.ultimate.test.decider.ITestResultDecider;
import de.uni_freiburg.informatik.ultimate.test.decider.TranslationTestResultDecider;
import de.uni_freiburg.informatik.ultimate.test.util.TestUtil;

/**
 * This testsuite tests whether the CACSL2BoogieTranslator translates C programs
 * to correct Boogie code. It runs CACSL2BoogieTranslator and BoogiePrinter on C
 * programs and compares the resulting Boogie file with a reference file.
 * 
 * <p>
 * The result of this test and of the comparison is decided in
 * {@link TranslationTestResultDecider}.
 * 
 * @author dietsch@informatik.uni-freiburg.de
 * 
 */
public class C2BoogieRegressionTestSuite extends AbstractRegressionTestSuite {

	private static String sRootFolder = TestUtil.getPathFromTrunk("examples/CToBoogieTranslation");

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
		return new TranslationTestResultDecider(runDefinition.selectPrimaryInputFile());
	}

	/**
	 * Deletes the temporary Boogie files that have been created after the
	 * execution of this testsuite. Will be called by the JUnit framework.
	 */
	@AfterClass
	public static void cleanupBoogiePrinterFiles() {

		final File root = getRootFolder(sRootFolder);

		Collection<File> files = TestUtil.getFiles(root, new String[] { ".bpl" });
		files = TestUtil.filterFiles(files, TEMPORARY_BOOGIE_FILENAME_PATTERN);

		if (files.isEmpty()) {
			System.out.println(String.format("No cleanup of %s necessary, no files matching the pattern %s have been found",
					sRootFolder, TEMPORARY_BOOGIE_FILENAME_PATTERN));
			return;
		}

		System.out.println(String.format("Begin cleanup of %s", sRootFolder));
		for (final File f : files) {
			try {
				if (f.delete()) {
					System.out.println(String.format("Sucessfully deleted %s", f.getAbsolutePath()));
				} else {
					System.out.println(String.format("Deleteing %s failed", f.getAbsolutePath()));
				}
			} catch (final SecurityException e) {
				System.err.println(String.format("Exception while deleting file %s", f));
				e.printStackTrace();
			}
		}
	}
}
