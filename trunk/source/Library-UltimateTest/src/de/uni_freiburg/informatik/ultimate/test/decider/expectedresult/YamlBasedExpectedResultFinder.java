/*
 * Copyright (C) 2019 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2019 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.test.decider.expectedresult;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;

import de.uni_freiburg.informatik.ultimate.test.UltimateRunDefinition;

/**
 * Workaround that will be improved in the next days.
 * Find the expected result for an SV-COMP benchmark. Starting from SV-COMP 2020
 * the expected results are given by YAML files. This class does not use a
 * proper YAML parser and is a hack that should work for the YAML files that are
 * currently in the competition repository.
 * https://github.com/sosy-lab/sv-benchmarks/
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
public class YamlBasedExpectedResultFinder<OVERALL_RESULT> extends AbstractExpectedResultFinder<OVERALL_RESULT> {
	private final String mPropertyFile;
	private final OVERALL_RESULT mPositiveResult;
	private final OVERALL_RESULT mNegativeResult;
	private static final String VERDICT_TRUE = "expected_verdict: true";
	private static final String VERDICT_FALSE = "expected_verdict: false";



	public YamlBasedExpectedResultFinder(final String propertyFile, final OVERALL_RESULT positiveResult,
			final OVERALL_RESULT negativeResult) {
		super();
		mPropertyFile = propertyFile;
		mPositiveResult = positiveResult;
		mNegativeResult = negativeResult;
	}



	@Override
	public void findExpectedResult(final UltimateRunDefinition ultimateRunDefinition) {
		final File file = ultimateRunDefinition.selectPrimaryInputFile();
		final String[] basenameAndExtension = file.getAbsolutePath().split("\\.(?=[^\\.]+$)");
		final String yamlFilename = basenameAndExtension[0] + ".yml";
		final File yamlFile = new File(yamlFilename);
		final BufferedReader br;
		try {
			br = new BufferedReader(new FileReader(yamlFile));
			String line = br.readLine();
			while (line != null) {
				if (line.contains(mPropertyFile)) {
					final String nextLine = br.readLine();
					if (nextLine == null) {
						super.mExpectedResult = null;
						super.mEvaluationStatus = ExpectedResultFinderStatus.ERROR;
						super.mExpectedResultEvaluation = "Cannot understand YAML file";
					} else {
						if (nextLine.contains(VERDICT_TRUE)) {
							super.mEvaluationStatus = ExpectedResultFinderStatus.EXPECTED_RESULT_FOUND;
							super.mExpectedResult = mPositiveResult;
							super.mExpectedResultEvaluation = "Expected result: " + mExpectedResult;
						} else if (nextLine.contains(VERDICT_FALSE)) {
							super.mEvaluationStatus = ExpectedResultFinderStatus.EXPECTED_RESULT_FOUND;
							super.mExpectedResult = mNegativeResult;
							super.mExpectedResultEvaluation = "Expected result: " + mExpectedResult;
						} else {
							super.mExpectedResult = null;
							super.mEvaluationStatus = ExpectedResultFinderStatus.ERROR;
							super.mExpectedResultEvaluation = "Cannot understand YAML file";
						}
					}
					br.close();
					return;
				}
				line = br.readLine();
			}
			super.mExpectedResult = null;
			super.mEvaluationStatus = ExpectedResultFinderStatus.NO_EXPECTED_RESULT_FOUND;
			super.mExpectedResultEvaluation = "YAML file does not contain expected result";
			br.close();
		} catch (final FileNotFoundException fnfe) {
			super.mExpectedResult = null;
			super.mEvaluationStatus = ExpectedResultFinderStatus.NO_EXPECTED_RESULT_FOUND;
			super.mExpectedResultEvaluation = "YAML file does not exist";
		} catch (final IOException e) {
			throw new AssertionError("unable to read file " + file);
		}
	}

}
