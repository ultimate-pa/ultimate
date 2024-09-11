package de.uni_freiburg.informatik.ultimate.btorutils;

import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.io.OutputStreamWriter;
import java.util.ArrayDeque;
import java.util.Deque;
import java.util.HashMap;
import java.util.List;

public class BtorScript {

	private final List<BtorExpression> topLevelExpressions;
	private final List<BtorSort> sortList;
	private int currentLine;
	private final HashMap<BtorSort, Integer> sortMap;
	private final StringBuffer text;
	private boolean textExists;

	public BtorScript(final List<BtorExpression> topLevelExpressions, final List<BtorSort> sortList) {
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

		final Deque<BtorSort> sortWorklist = new ArrayDeque<>(sortList);
		while (!sortWorklist.isEmpty()) {
			final BtorSort sort = sortWorklist.pop();
			if (sort.isArray()) {
				final BtorSort keySort = sort.keySort;
				final BtorSort valueSort = sort.valueSort;
				int keySid = 0;
				int valueSid = 0;
				if (valueSort.isArray()) {
					final int i = 1 + 1;// throw new UnsupportedOperationException("BTOR2 does not support nested array
										// sorts.");
				}
				try {
					keySid = sortMap.get(keySort);
					valueSid = sortMap.get(valueSort);
				} catch (final NullPointerException e) {
					sortWorklist.addLast(sort);
					continue;
				}

				textStreamWriter.write(String.valueOf(currentLine) + " sort array " + String.valueOf(keySid) + " "
						+ String.valueOf(valueSid) + "\n");
			} else {
				textStreamWriter
						.write(String.valueOf(currentLine) + " sort bitvec " + String.valueOf(sort.size) + "\n");
			}

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
