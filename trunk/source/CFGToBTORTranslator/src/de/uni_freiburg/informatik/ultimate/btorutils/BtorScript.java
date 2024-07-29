package de.uni_freiburg.informatik.ultimate.btorutils;

import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.io.OutputStreamWriter;
import java.util.HashMap;
import java.util.List;

public class BtorScript {

	private final List<BtorExpression> topLevelExpressions;
	private final List<Integer> sortList;
	private int currentLine;
	private final HashMap<Integer, Integer> sortMap;
	private final StringBuffer text;
	private boolean textExists;

	public BtorScript(final List<BtorExpression> topLevelExpressions, final List<Integer> sortList) {
		this.topLevelExpressions = topLevelExpressions;
		this.sortList = sortList;
		sortMap = new HashMap<>();
		currentLine = 1;
		text = new StringBuffer();
		textExists = false;
	}

	public void dumpScript(final OutputStreamWriter writer) throws IOException {
		if (textExists == true) {
			writer.write(text.toString());
			writer.flush();
			return;
		}
		final ByteArrayOutputStream textStream = new ByteArrayOutputStream();
		final OutputStreamWriter textStreamWriter = new OutputStreamWriter(textStream);

		for (final int sort : sortList) {
			textStreamWriter.write(String.valueOf(currentLine) + " sort bitvec " + String.valueOf(sort) + "\n");
			sortMap.put(sort, currentLine);
			currentLine++;
			textStreamWriter.flush();
		}
		for (final BtorExpression topLevelExpression : topLevelExpressions) {
			currentLine = topLevelExpression.dumpExpression(currentLine, textStreamWriter, sortMap);
		}
		textStreamWriter.flush();
		text.append(textStream.toString());
		writer.write(text.toString());
		writer.flush();
		textExists = true;
	}
}
