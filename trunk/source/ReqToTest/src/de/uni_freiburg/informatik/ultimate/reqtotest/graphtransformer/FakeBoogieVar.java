package de.uni_freiburg.informatik.ultimate.reqtotest.graphtransformer;

import java.util.Collections;

import de.uni_freiburg.informatik.ultimate.core.model.models.IBoogieType;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.NoopScript;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.TypeSortTranslator;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;

/**
 * A simulating implementation of {@link IProgramVar}.
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public final class FakeBoogieVar implements IProgramVar {

	private static final long serialVersionUID = 1L;

	private static final Script SCRIPT_MOCK = new MockScript();

	private final String mId;
	private final Sort mSort;

	public FakeBoogieVar(final IBoogieType type, final String identifier) {
		mId = identifier;
		mSort = new TypeSortTranslator(Collections.emptyList(), SCRIPT_MOCK, null).constructSort(type, a -> null);
	}

	@Override
	public String getGloballyUniqueId() {
		return mId;
	}

	@Override
	public ApplicationTerm getDefaultConstant() {
		throw new UnsupportedOperationException("Temporary IBoogieVars dont have default constants.");
	}

	@Override
	public String toString() {
		return mId;
	}

	@Override
	public Sort getSort() {
		return mSort;
	}

	private static final class MockScript extends NoopScript {
		public MockScript() {
			super(new Theory(Logics.ALL));
		}
	}

	@Override
	public Term getTerm() {
		throw new UnsupportedOperationException("Temporary IBoogieVars dont have terms.");
	}

	@Override
	public boolean isGlobal() {
		throw new UnsupportedOperationException("Temporary IProgramVar");
	}

	@Override
	public String getProcedure() {
		throw new UnsupportedOperationException("Temporary IProgramVar");
	}

	@Override
	public boolean isOldvar() {
		throw new UnsupportedOperationException("Temporary IProgramVar");
	}

	@Override
	public TermVariable getTermVariable() {
		throw new UnsupportedOperationException("Temporary IProgramVar");
	}

	@Override
	public ApplicationTerm getPrimedConstant() {
		throw new UnsupportedOperationException("Temporary IProgramVar");
	}
}
