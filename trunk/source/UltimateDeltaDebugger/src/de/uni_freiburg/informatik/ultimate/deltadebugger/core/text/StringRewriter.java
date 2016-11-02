package de.uni_freiburg.informatik.ultimate.deltadebugger.core.text;

public class StringRewriter extends AbstractTextRewriter {
	private final String mText;

	public StringRewriter(final String text) {
		mText = text;
	}

	@Override
	protected int getOriginalLength() {
		return mText.length();
	}

	@Override
	protected String getOriginalText() {
		return mText;
	}
}
