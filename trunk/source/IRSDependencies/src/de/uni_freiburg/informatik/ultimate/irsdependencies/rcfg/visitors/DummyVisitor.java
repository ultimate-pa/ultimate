package de.uni_freiburg.informatik.ultimate.irsdependencies.rcfg.visitors;

public class DummyVisitor extends SimpleRCFGVisitor {

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
