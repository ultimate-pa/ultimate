/*
 * Copyright (C) 2014-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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
package de.uni_freiburg.informatik.ultimate.test.decider.expectedresult;

import java.io.File;
import java.util.Collections;
import java.util.HashSet;
import java.util.Map;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.test.UltimateRunDefinition;
import de.uni_freiburg.informatik.ultimate.test.util.TestUtil;

import java.util.Set;

/**
 * Find the expected result for a file using keywords that occur in
 * <ul>
 * <li>the filename of the input,
 * <li>the path of the input (without the filename), or
 * <li>the first line of the input.
 * <ul>
 * For each occurrence the keywords have to be given as a Map<String, OVERALL_RESULT>. If you do not want to check some
 * occurrences (e.g., do not want to check the path, you may use an empty Map or null.
 * 
 * This IExpectedResultFinder takes neither settings nor toolchain into account.
 * 
 * @author heizmann@informatik.uni-freiburg.de
 *
 * @param <OVERALL_RESULT>
 */
public class KeywordBasedExpectedResultFinder<OVERALL_RESULT> implements IExpectedResultFinder<OVERALL_RESULT> {
	private final Map<String, OVERALL_RESULT> m_FilenameKeywords;
	private final Map<String, OVERALL_RESULT> m_PathKeywords;
	private final Map<String, OVERALL_RESULT> m_FirstlineKeywords;

	OVERALL_RESULT m_ExpectedResult;
	ExpectedResultFinderStatus m_EvaluationStatus;
	String m_ExpectedResultEvaluation;

	public KeywordBasedExpectedResultFinder(Map<String, OVERALL_RESULT> filenameKeywords,
			Map<String, OVERALL_RESULT> pathKeywords, Map<String, OVERALL_RESULT> firstlineKeywords) {
		if (filenameKeywords == null) {
			m_FilenameKeywords = Collections.emptyMap();
		} else {
			m_FilenameKeywords = filenameKeywords;
		}
		if (pathKeywords == null) {
			m_PathKeywords = Collections.emptyMap();
		} else {
			m_PathKeywords = pathKeywords;
		}
		if (firstlineKeywords == null) {
			m_FirstlineKeywords = Collections.emptyMap();
		} else {
			m_FirstlineKeywords = firstlineKeywords;
		}
	}

	@Override
	public void findExpectedResult(UltimateRunDefinition ultimateRunDefinition) {
		File file = ultimateRunDefinition.selectPrimaryInputFile();
		Set<OVERALL_RESULT> expectedResult = new HashSet<OVERALL_RESULT>();
		if (file != null) {
			String filename = file.getName();
			for (Entry<String, OVERALL_RESULT> entry : m_FilenameKeywords.entrySet()) {
				if (filename.matches(entry.getKey())) {
					expectedResult.add(entry.getValue());
				}
			}
			String folder = file.getParent();
			for (Entry<String, OVERALL_RESULT> entry : m_PathKeywords.entrySet()) {
				if (folder.contains(entry.getKey())) {
					expectedResult.add(entry.getValue());
				}
			}
			String firstline = TestUtil.extractFirstLine(file);
			// 2015-10-04 Matthias: firstline != null is a workaround that I used
			// for emtpy files (SV-COMP benchmark set contained empty files).
			if (firstline != null) {
				for (Entry<String, OVERALL_RESULT> entry : m_FirstlineKeywords.entrySet()) {
					if (firstline.contains(entry.getKey())) {
						expectedResult.add(entry.getValue());
					}
				}
			}
		}
		if (expectedResult.size() == 0) {
			m_ExpectedResult = null;
			m_EvaluationStatus = ExpectedResultFinderStatus.NO_EXPECTED_RESULT_FOUND;
			m_ExpectedResultEvaluation = "Neither filename nor path nor first line contains a keyword that defines the expected result";
		} else if (expectedResult.size() == 1) {
			m_ExpectedResult = expectedResult.iterator().next();
			m_EvaluationStatus = ExpectedResultFinderStatus.EXPECTED_RESULT_FOUND;
			m_ExpectedResultEvaluation = "Expected result: " + m_ExpectedResult;
		} else {
			m_EvaluationStatus = ExpectedResultFinderStatus.ERROR;
			m_ExpectedResultEvaluation = "Error: annotation given by keywords is inconsitent";
		}
	}

	@Override
	public String getExpectedResultFinderMessage() {
		return m_ExpectedResultEvaluation;
	}

	@Override
	public OVERALL_RESULT getExpectedResult() {
		return m_ExpectedResult;
	}

	@Override
	public ExpectedResultFinderStatus getExpectedResultFinderStatus() {
		return m_EvaluationStatus;
	}

}
