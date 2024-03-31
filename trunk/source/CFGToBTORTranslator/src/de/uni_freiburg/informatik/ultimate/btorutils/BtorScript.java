package de.uni_freiburg.informatik.ultimate.btorutils;

import java.io.IOException;
import java.io.OutputStreamWriter;
import java.util.HashMap;
import java.util.List;

public class BtorScript {

	private final List<BtorExpression> topLevelExpressions;
	private final List<Integer> sortList;
	private int currentLine;
	private final HashMap<Integer, Integer> sortMap;

	public BtorScript(final List<BtorExpression> topLevelExpressions, final List<Integer> sortList) {
		this.topLevelExpressions = topLevelExpressions;
		this.sortList = sortList;
		sortMap = new HashMap<>();
		currentLine = 1;
	}

	public void dumpScript(final OutputStreamWriter writer) throws IOException {
		for (final int sort : sortList) {
			writer.write(String.valueOf(currentLine) + " sort bitvec " + String.valueOf(sort) + "\n");
			sortMap.put(sort, currentLine);
			currentLine++;
		}
		for (final BtorExpression topLevelExpression : topLevelExpressions) {
			currentLine = topLevelExpression.dumpExpression(currentLine, writer, sortMap);
		}
	}
}
