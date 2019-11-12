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
import java.io.FileReader;
import java.io.IOException;

import de.uni_freiburg.informatik.ultimate.test.UltimateRunDefinition;

/**
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
	private static final String VERDICT_TRUE = "expected_verdict: true";
	private static final String VERDICT_FALSE = "expected_verdict: true";

	public YamlBasedExpectedResultFinder(final String propertyFile) {
		mPropertyFile = propertyFile;
	}

	@Override
	public void findExpectedResult(final UltimateRunDefinition ultimateRunDefinition) {
		final File file = ultimateRunDefinition.selectPrimaryInputFile();
		final String[] basenameAndExtension = file.getAbsolutePath().split("\\.(?=[^\\.]+$)");
		final String yamlFilename = file.getAbsolutePath() + ".yaml";
		final File yamlFile = new File(yamlFilename);
		BufferedReader br;
		try {
			br = new BufferedReader(new FileReader(file));
			String line = br.readLine();
			while (line != null) {
				line = br.readLine();
			}
			br.close();
		} catch (final IOException e) {
			throw new AssertionError("unable to read file " + file);
		}
	}

}
