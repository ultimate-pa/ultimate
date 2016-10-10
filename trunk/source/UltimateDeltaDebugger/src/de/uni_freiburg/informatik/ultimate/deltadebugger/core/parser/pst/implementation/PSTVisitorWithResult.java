package de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.implementation;

import java.util.Optional;

import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTVisitor;

public class PSTVisitorWithResult<T> implements IPSTVisitor {
	private Optional<T> result;

	public PSTVisitorWithResult() {
		result = Optional.empty();
	}

	public PSTVisitorWithResult(final T initialValue) {
		result = Optional.of(initialValue);
	}

	public Optional<T> getResult() {
		return result;
	}

	public void setResult(final T value) {
		result = Optional.of(value);
	}
}