package de.uni_freiburg.informatik.ultimate.civlizer;

import java.io.PrintWriter;
import java.io.OutputStream;

final class StringBuilderWriter extends PrintWriter {

    private StringBuilder mResult;

    StringBuilderWriter() {
        super(OutputStream.nullOutputStream()); // to be change TODO
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
        mResult.append(s);
    }

    @Override
    public void println(String s) {
        mResult.append(s).append("\n");
    }
}