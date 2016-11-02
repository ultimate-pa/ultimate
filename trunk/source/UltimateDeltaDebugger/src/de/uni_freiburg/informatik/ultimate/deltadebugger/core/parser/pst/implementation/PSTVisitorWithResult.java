package de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.implementation;

import java.util.Optional;

import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTVisitor;

public class PSTVisitorWithResult<T> implements IPSTVisitor {
	private Optional<T> mResult;

	public PSTVisitorWithResult() {
		mResult = Optional.empty();
	}

	public PSTVisitorWithResult(final T initialValue) {
		mResult = Optional.of(initialValue);
	}

	public Optional<T> getResult() {
		return mResult;
	}

	public void setResult(final T value) {
		mResult = Optional.of(value);
	}
}
