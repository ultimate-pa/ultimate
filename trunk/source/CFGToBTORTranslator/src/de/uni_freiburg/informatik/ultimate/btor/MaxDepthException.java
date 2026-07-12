package de.uni_freiburg.informatik.ultimate.btor;

public class MaxDepthException extends Exception {

	public int currentLine;

	public MaxDepthException(final int currentLine) {
		this.currentLine = currentLine;
	}
}
