package de.uni_freiburg.informatik.ultimate.irsdependencies.rcfg.visitors;

import org.apache.log4j.Logger;

public class DummyVisitor extends SimpleRCFGVisitor {

	public DummyVisitor(Logger logger) {
		super(logger);
	}

	@Override
	public boolean performedChanges() {
		return false;
	}

	@Override
	public boolean abortCurrentBranch() {
		return false;
	}

	@Override
	public boolean abortAll() {
		return false;
	}

}
