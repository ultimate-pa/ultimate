package de.uni_freiburg.informatik.ultimate.lib.sifa.test;

import java.util.Collections;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramFunction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 * Simple mock predicate for testing purposes.
 */
public class MockPredicate implements IPredicate {

	private static final long serialVersionUID = 1L;

	private final String mName;

	private MockPredicate(final String name) {
		mName = name;
	}

	public static MockPredicate of(final String name) {
		return new MockPredicate(name);
	}

	@Override
	public Set<IProgramVar> getVars() {
		return Collections.emptySet();
	}

	@Override
	public Set<IProgramFunction> getFuns() {
		return Collections.emptySet();
	}

	@Override
	public Term getFormula() {
		throw new UnsupportedOperationException("MockPredicate has no formula");
	}

	@Override
	public Term getClosedFormula() {
		throw new UnsupportedOperationException("MockPredicate has no formula");
	}

	@Override
	public String toString() {
		return mName;
	}

	@Override
	public int hashCode() {
		return mName.hashCode();
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		}
		if (!(obj instanceof MockPredicate)) {
			return false;
		}
		return mName.equals(((MockPredicate) obj).mName);
	}

	public String getName() {
		return mName;
	}
}
