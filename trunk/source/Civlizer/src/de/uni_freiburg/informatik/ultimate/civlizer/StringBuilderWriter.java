package de.uni_freiburg.informatik.ultimate.civlizer;

import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintWriter;

final class StringBuilderWriter extends PrintWriter {

	private StringBuilder mResult;

	StringBuilderWriter() throws IOException {
		super(new FileWriter("/tmp/temporary.bpl")); // to be change TODO
		mResult = new StringBuilder();
	}

	StringBuilder getResult() {
		return mResult;
	}

	@Override
	public String toString() {
		return mResult.toString();
	}

	@Override
	public void print(String s) {
		super.print(s);
		mResult.append(s);
	}

	@Override
	public void println(String s) {
		super.println(s);
		mResult.append(s).append("\n");
	}
}