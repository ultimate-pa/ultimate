package de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.biesenb;

import java.util.Arrays;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.BoogieNonOldVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.BoogieOldVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.ProgramVarUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.PredicateUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;

final class TestPredicate implements IPredicate {

	private final Set<IProgramVar> mVars;
	private final Term mClosedFormula;
	private final Term mFormula;

	public TestPredicate(final Term formula, final Set<IProgramVar> vars, final Script script) {
		mVars = vars;
		mFormula = formula;
		mClosedFormula = PredicateUtils.computeClosedFormula(formula, vars, script);
	}

	@Override
	public String[] getProcedures() {
		return new String[0];
	}

	@Override
	public Set<IProgramVar> getVars() {
		return mVars;
	}

	@Override
	public Term getFormula() {
		return mFormula;
	}

	@Override
	public Term getClosedFormula() {
		return mClosedFormula;
	}

	@Override
	public String toString() {
		return getFormula().toStringDirect();
	}

	public static TestPredicate pred(final Script script, final String op, final IProgramVar var, final int value) {
		return new TestPredicate(script.term(op, var.getTermVariable(), script.numeral(String.valueOf(value))),
				Collections.singleton(var), script);
	}

	public static TestPredicate neg(final Script script, final TestPredicate pred) {
		return new TestPredicate(script.term("not", pred.getFormula()), pred.getVars(), script);
	}

	public static TestPredicate and(final Script script, final TestPredicate... preds) {
		if (preds == null || preds.length < 2) {
			throw new IllegalArgumentException();
		}
		final List<Term> operands = Arrays.stream(preds).map(a -> a.getFormula()).collect(Collectors.toList());
		final Set<IProgramVar> vars = Arrays.stream(preds).map(a -> a.getVars()).reduce(new HashSet<>(),
				(a, b) -> DataStructureUtils.union(a, b));
		return new TestPredicate(SmtUtils.and(script, operands), vars, script);
	}

	public static IProgramNonOldVar constructProgramVar(final ManagedScript mMgdScript, final String identifier) {
		BoogieOldVar oldVar;
		final Script script = mMgdScript.getScript();
		final Object lock = new Object();
		final Sort sort = SmtSortUtils.getIntSort(script);
		{
			final boolean isOldVar = true;
			final String name = ProgramVarUtils.buildBoogieVarName(identifier, null, true, isOldVar);
			final TermVariable termVariable = script.variable(name, sort);
			mMgdScript.lock(lock);
			final ApplicationTerm defaultConstant =
					ProgramVarUtils.constructDefaultConstant(mMgdScript, lock, sort, name);
			final ApplicationTerm primedConstant =
					ProgramVarUtils.constructPrimedConstant(mMgdScript, lock, sort, name);
			mMgdScript.unlock(lock);
			oldVar = new BoogieOldVar(identifier, null, termVariable, defaultConstant, primedConstant);
		}
		BoogieNonOldVar nonOldVar;
		{
			final boolean isOldVar = false;
			final String name = ProgramVarUtils.buildBoogieVarName(identifier, null, true, isOldVar);
			final TermVariable termVariable = script.variable(name, sort);
			mMgdScript.lock(lock);
			final ApplicationTerm defaultConstant =
					ProgramVarUtils.constructDefaultConstant(mMgdScript, lock, sort, name);
			final ApplicationTerm primedConstant =
					ProgramVarUtils.constructPrimedConstant(mMgdScript, lock, sort, name);
			mMgdScript.unlock(lock);
			nonOldVar = new BoogieNonOldVar(identifier, null, termVariable, defaultConstant, primedConstant, oldVar);
		}
		oldVar.setNonOldVar(nonOldVar);
		return nonOldVar;
	}

}