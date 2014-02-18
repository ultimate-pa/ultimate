package de.uni_freiburg.informatik.ultimateregressiontest.translation;

import java.io.File;
import java.io.IOException;
import java.util.Collection;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;
import java.util.Map.Entry;

import org.apache.log4j.Logger;
import org.eclipse.core.runtime.Path;

import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.result.ExceptionOrErrorResult;
import de.uni_freiburg.informatik.ultimate.result.IResult;
import de.uni_freiburg.informatik.ultimate.result.SyntaxErrorResult;
import de.uni_freiburg.informatik.ultimatetest.ITestResultDecider;
import de.uni_freiburg.informatik.ultimatetest.Util;

class TranslationTestResultDecider implements ITestResultDecider {

	private String mInputFile;

	public TranslationTestResultDecider(String inputFile) {
		mInputFile = inputFile;
	}

	@Override
	public boolean isResultFail() {

		Logger log = Logger.getLogger(TranslationTestResultDecider.class);
		Collection<String> customMessages = new LinkedList<String>();
		customMessages.add("Expecting results to not contain SyntaxErrorResult or ExceptionOrErrorResult");
		boolean fail = false;
		Set<Entry<String, List<IResult>>> resultSet = UltimateServices.getInstance().getResultMap().entrySet();
		if (resultSet.size() == 0) {
			customMessages.add("There were no results (this is good for this test)");
		} else {
			for (Entry<String, List<IResult>> x : resultSet) {
				for (IResult result : x.getValue()) {
					customMessages.add(String.format("Result %s: %s", result.getShortDescription(),
							result.getLongDescription()));
					if (result instanceof SyntaxErrorResult) {
						fail = true;
					}
					if (result instanceof ExceptionOrErrorResult) {
						fail = true;
					}
				}
			}
		}

		if (!fail) {
			// there were no exceptions
			// we need to compare the existing .bpl file against the one
			// generated
			// by Boogie Printer
			// if there are no existing files, we just assume it was only a test
			// against syntax errors

			File inputFile = new File(mInputFile);
			String inputFileNameWithoutEnding = inputFile.getName().replaceAll("\\.c", "");
			File desiredBplFile = new File(String.format("%s%s%s%s", inputFile.getParentFile().getAbsolutePath(),
					Path.SEPARATOR, inputFileNameWithoutEnding, ".bpl"));
			File actualBplFile = Util.getFilesRegex(inputFile.getParentFile(),
					new String[] { String.format(".*%s\\.bpl", inputFileNameWithoutEnding) }).toArray(new File[1])[0];
			if (actualBplFile != null) {

				try {
					String desiredContent = Util.readFile(desiredBplFile);
					String actualContent = Util.readFile(actualBplFile);

					if (!desiredContent.equals(actualContent)) {
						customMessages.add("Desired content does not match actual content.");
						customMessages.add("Desired content:");
						for(String s : desiredContent.split("\n")){
							customMessages.add(s);
						}
						customMessages.add("Actual content:");
						for(String s : actualContent.split("\n")){
							customMessages.add(s);
						}
						fail = true;
					}

				} catch (IOException e) {
					e.printStackTrace();
					fail = true;
				}
			} else {
				customMessages.add(String.format("There is no .bpl file for %s!", mInputFile));
			}

		}

		Util.logResults(log, mInputFile, fail, customMessages);
		return fail;
	}

	@Override
	public boolean isResultFail(Exception e) {
		return true;
	}

}