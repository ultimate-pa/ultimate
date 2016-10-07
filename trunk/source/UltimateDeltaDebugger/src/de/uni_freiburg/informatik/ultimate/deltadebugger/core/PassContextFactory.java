package de.uni_freiburg.informatik.ultimate.deltadebugger.core;

@FunctionalInterface
public interface PassContextFactory {
	PassContext create(String source);
}