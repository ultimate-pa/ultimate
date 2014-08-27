package de.uni_freiburg.informatik.ultimatetest.decider.expectedResult;

import java.io.File;
import java.util.HashSet;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimatetest.UltimateRunDefinition;
import de.uni_freiburg.informatik.ultimatetest.decider.expectedResult.ExpectedResultEvaluation.EvaluationStatus;
import de.uni_freiburg.informatik.ultimatetest.util.Util;

public class KeywordBasedExpectedResultEvaluation<OVERALL_RESULT> implements
		ExpectedResultEvaluation<OVERALL_RESULT> {
	private final Map<String, OVERALL_RESULT> m_FilenameKeywords;
	private final Map<String, OVERALL_RESULT> m_FolderKeywords;	
	private final Map<String, OVERALL_RESULT> m_FirstlineKeywords;
	
	
	OVERALL_RESULT m_ExpectedResult;
	EvaluationStatus m_EvaluationStatus;
	String m_ExpectedResultEvaluation;

	public KeywordBasedExpectedResultEvaluation(
			Map<String, OVERALL_RESULT> filenameKeywords, 
			Map<String, OVERALL_RESULT> folderKeywords,
			Map<String, OVERALL_RESULT> firstlineKeywords) {
		m_FilenameKeywords = filenameKeywords;
		m_FolderKeywords = folderKeywords;
		m_FirstlineKeywords = firstlineKeywords;
	}
	
	@Override
	public void evaluateExpectedResult(
			UltimateRunDefinition ultimateRunDefinition) {
		File file = ultimateRunDefinition.getInput();
		Set<OVERALL_RESULT> expectedResult= new HashSet<OVERALL_RESULT>();
		String filename = file.getName();
		for (Entry<String, OVERALL_RESULT> entry  : m_FilenameKeywords.entrySet()) {
			if (filename.contains(entry.getKey())) {
				expectedResult.add(entry.getValue());
			}
		}
		String folder = file.getParent();
		for (Entry<String, OVERALL_RESULT> entry  : m_FolderKeywords.entrySet()) {
			if (folder.contains(entry.getKey())) {
				expectedResult.add(entry.getValue());
			}
		}
		String firstline = Util.extractFirstLine(file);
		for (Entry<String, OVERALL_RESULT> entry  : m_FirstlineKeywords.entrySet()) {
			if (firstline.contains(entry.getKey())) {
				expectedResult.add(entry.getValue());
			}
		}
		if (expectedResult.size() == 0) {
			m_ExpectedResult = null;
			m_EvaluationStatus = EvaluationStatus.UNKNOWN;
			m_ExpectedResultEvaluation = "Neither filename nor folder nor first line contains a keyword that defines the expected result";
		} else if (expectedResult.size() == 1) {
			m_ExpectedResult = expectedResult.iterator().next();
			m_EvaluationStatus = EvaluationStatus.DETERMINED;
			m_ExpectedResultEvaluation = "Expected result: " + m_ExpectedResult;
		} else {
			m_EvaluationStatus = EvaluationStatus.ERROR;
			m_ExpectedResultEvaluation = "Error: annotation given by keywords is inconsitent";
		}
	}

	@Override
	public String getExpectedResultEvaluationMessage() {
		return m_ExpectedResultEvaluation;
	}

	@Override
	public OVERALL_RESULT getExpectedResult() {
		return m_ExpectedResult;
	}

	@Override
	public EvaluationStatus getExpectedResultEvaluationStatus() {
		return m_EvaluationStatus;
	}

}
