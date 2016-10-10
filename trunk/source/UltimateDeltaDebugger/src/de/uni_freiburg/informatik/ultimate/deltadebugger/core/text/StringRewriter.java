package de.uni_freiburg.informatik.ultimate.deltadebugger.core.text;

public class StringRewriter extends AbstractTextRewriter {
	private final String text;

	public StringRewriter(final String text) {
		this.text = text;
	}

	@Override
	protected int getOriginalLength() {
		return text.length();
	}

	@Override
	protected String getOriginalText() {
		return text;
	}
}
