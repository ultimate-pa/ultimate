/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE UnitTest Library.
 * 
 * The ULTIMATE UnitTest Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE UnitTest Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE UnitTest Library. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE UnitTest Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE UnitTest Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.test.decider;

import java.io.File;
import java.io.IOException;
import java.util.Collection;
import java.util.LinkedList;
import java.util.List;
import java.util.Map.Entry;
import java.util.Optional;
import java.util.Set;

import org.eclipse.core.runtime.IPath;

import de.uni_freiburg.informatik.ultimate.core.lib.results.ExceptionOrErrorResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.SyntaxErrorResult;
import de.uni_freiburg.informatik.ultimate.core.lib.results.TypeErrorResult;
import de.uni_freiburg.informatik.ultimate.core.model.results.IResult;
import de.uni_freiburg.informatik.ultimate.core.model.results.ITimeoutResult;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IResultService;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.test.util.TestUtil;
import de.uni_freiburg.informatik.ultimate.util.CoreUtil;

/**
 * 
 * The {@link TranslationTestResultDecider} is a {@link TestResultDecider} that checks whether a translating toolchain
 * fails or not.
 * 
 * The decider will fail if the results contain a {@link TypeErrorResult}, {@link SyntaxErrorResult},
 * {@link ExceptionOrErrorResult}, or a {@link ITimeoutResult}.
 * 
 * Additionally, the decider can check whether the output of the BoogiePrinter plugin is as expected. This is done only
 * if there is a desired translation file and an appropriately configured BoogiePrinter plugin that generates a
 * BoogieFile.
 * 
 * If there is a .bpl file besides the input file that is named like the input file but with the .bpl extension (e.g.,
 * foo.c and foo.bpl), this file is used as desired translation. This decider then finds the auto-generated format of
 * BoogiePrinter (i.e., BoogiePrinter_inputfilename_UID...) besides the input and compares it line by line with the
 * desired translation. If they do not match, the test fails.
 * 
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * 
 */
public class TranslationTestResultDecider extends TestResultDecider {

	private final String mInputFile;

	public TranslationTestResultDecider(final String inputFile) {
		mInputFile = inputFile;
	}

	public TranslationTestResultDecider(final File inputFile) {
		mInputFile = inputFile.getAbsolutePath();
	}

	@Override
	public TestResult getTestResult(final IUltimateServiceProvider services) {

		setResultCategory("");
		setResultMessage("");

		final IResultService resultService = services.getResultService();
		final ILogger log = services.getLoggingService().getLogger(TranslationTestResultDecider.class);
		final Collection<String> customMessages = new LinkedList<>();
		customMessages.add("Expecting results to have a counterexample that matches the .bpl file, "
				+ "and no generic result \"Unhandled Backtranslation\"");
		boolean fail = false;

		final Set<Entry<String, List<IResult>>> resultSet = resultService.getResults().entrySet();
		if (resultSet.isEmpty()) {
			setResultCategory("No results");
			customMessages.add("There were no results (this is good for this test)");
		} else {
			for (final Entry<String, List<IResult>> x : resultSet) {
				for (final IResult result : x.getValue()) {
					if (result instanceof TypeErrorResult || result instanceof SyntaxErrorResult
							|| result instanceof ExceptionOrErrorResult || result instanceof ITimeoutResult) {
						setResultCategory(result.getShortDescription());
						setResultMessage(result.getShortDescription());
						fail = true;
						break;
					}
				}
			}
		}

		if (!fail) {
			// There were no exceptions.
			// We need to compare the existing .bpl file against the one
			// generated by Boogie Printer.
			// If there are no existing files, we just assume it was only a test
			// against syntax errors.

			final File inputFile = new File(mInputFile);
			final String inputFileNameWithoutEnding = inputFile.getName().replaceAll("\\.c", "");
			final File desiredBplFile = new File(String.format("%s%s%s%s", inputFile.getParentFile().getAbsolutePath(),
					IPath.SEPARATOR, inputFileNameWithoutEnding, ".bpl"));

			final String actualFileRegex = String.format(".*BoogiePrinter_%s.*\\.bpl", inputFileNameWithoutEnding);
			final Optional<File> actualBplFile = TestUtil
					.getFilesRegex(inputFile.getParentFile(), new String[] { actualFileRegex }).stream().findFirst();
			if (actualBplFile.isPresent() && desiredBplFile.exists()) {

				try {
					final String desiredContent = CoreUtil.readFile(desiredBplFile);
					final String actualContent = CoreUtil.readFile(actualBplFile.get());

					if (!desiredContent.equals(actualContent)) {
						final String message = "Desired content does not match actual content.";
						setResultCategory("Mismatch between .bpl and .c");
						setResultMessage(message);
						customMessages.add(message);
						customMessages.add("--- Desired content ---");
						addMultilineString(customMessages, desiredContent);
						customMessages.add("--- Actual content ---");
						addMultilineString(customMessages, actualContent);
						fail = true;
					} else {
						setResultCategory(".bpl file equals expected .bpl file");
					}

				} catch (final IOException e) {
					setResultCategory(e.getMessage());
					setResultMessage(e.toString());
					e.printStackTrace();
					fail = true;
				}
			} else {
				if (getResultCategory().isEmpty() && !fail) {
					setResultCategory("no .bpl file for comparison, but no reason to fail");
				}
				customMessages.add(String.format("There is no .bpl file for %s!", mInputFile));
			}

		}

		TestUtil.logResults(log, mInputFile, fail, customMessages, resultService);
		return fail ? TestResult.FAIL : TestResult.SUCCESS;
	}

	private static void addMultilineString(final Collection<String> customMessages, final String actualContent) {
		for (final String s : actualContent.split(CoreUtil.getPlatformLineSeparator())) {
			customMessages.add(s);
		}
	}

	@Override
	public TestResult getTestResult(final IUltimateServiceProvider services, final Throwable e) {
		return TestResult.FAIL;
	}

}
