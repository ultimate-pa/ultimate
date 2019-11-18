package de.uni_freiburg.informatik.ultimate.lib.mcr;

import java.util.List;
import java.util.Objects;

import de.uni_freiburg.informatik.ultimate.lib.mcr.Mcr.IWriteRelation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Util;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;

public class InterpolantBasedWriteRelation<LETTER extends IIcfgTransition<?>> implements IWriteRelation<LETTER> {
	private final Script mScript;
	private final boolean mUseAbstraction;

	public InterpolantBasedWriteRelation(final Script script, final boolean useAbstraction) {
		mScript = script;
		mUseAbstraction = useAbstraction;
	}

	@Override
	public boolean canBeReplacedBy(final LETTER write1, final LETTER write2, final IProgramVar var,
			final List<LETTER> trace, final List<IPredicate> interpolants) {
		if (Objects.equals(write1, write2)) {
			return true;
		}
		final Term post1 = getPostcondition(write1, var, trace, interpolants);
		final Term post2 = getPostcondition(write2, var, trace, interpolants);
		return Util.checkSat(mScript, SmtUtils.and(mScript, post1, SmtUtils.not(mScript, post2))) == LBool.UNSAT;
	}

	// TODO: Cache this?
	private Term getPostcondition(final LETTER action, final IProgramVar var, final List<LETTER> trace,
			final List<IPredicate> interpolants) {
		if (action == null) {
			return mScript.term("true");
		}
		final int index = trace.indexOf(action);
		if (index == trace.size() - 1) {
			return mScript.term("false");
		}
		final Term formula = interpolants.get(index).getClosedFormula();
		// TODO: Somehow abstract other variables away
		if (mUseAbstraction) {
			throw new UnsupportedOperationException("Abstraction of variables is not supported yet.");
		}
		return formula;
	}
}
