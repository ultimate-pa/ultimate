package de.uni_freiburg.informatik.ultimate.smtinterpol.delta;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.logic.Assignments;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.Model;
import de.uni_freiburg.informatik.ultimate.logic.NoopScript;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

public class ParseScript extends NoopScript {
	
	private List<Cmd> m_Cmds = new ArrayList<Cmd>();
	
	public List<Cmd> getCmds() {
		return m_Cmds;
	}

	@Override
	public void setLogic(Logics logic) throws UnsupportedOperationException {
		super.setLogic(logic);
		m_Cmds.add(new SetLogic(logic));
	}

	@Override
	public void setOption(String opt, Object value)
			throws UnsupportedOperationException, SMTLIBException {
		m_Cmds.add(new SetterCmd("set-option", opt, value));
	}

	@Override
	public void setInfo(String info, Object value) {
		m_Cmds.add(new SetterCmd("set-info", info, value));
	}

	@Override
	public void declareSort(String sort, int arity) throws SMTLIBException {
		super.declareSort(sort, arity);
		m_Cmds.add(new DeclareSort(sort, arity));
	}

	@Override
	public void defineSort(String sort, Sort[] sortParams, Sort definition)
			throws SMTLIBException {
		super.defineSort(sort, sortParams, definition);
		m_Cmds.add(new DefineSort(sort, sortParams, definition));
	}

	@Override
	public void declareFun(String fun, Sort[] paramSorts, Sort resultSort)
			throws SMTLIBException {
		super.declareFun(fun, paramSorts, resultSort);
		m_Cmds.add(new DeclareFun(fun, paramSorts, resultSort));
	}

	@Override
	public void defineFun(String fun, TermVariable[] params, Sort resultSort,
			Term definition) throws SMTLIBException {
		super.defineFun(fun, params, resultSort, definition);
		m_Cmds.add(new DefineFun(fun, params, resultSort, definition));
	}

	@Override
	public void push(int levels) {
		super.push(levels);
		m_Cmds.add(new ScopeCmd("push", levels));
	}

	@Override
	public void pop(int levels) throws SMTLIBException {
		super.pop(levels);
		m_Cmds.add(new ScopeCmd("pop", levels));
	}

	@Override
	public LBool assertTerm(Term term) throws SMTLIBException {
		m_Cmds.add(new OneTermCmd("assert", term));
		return LBool.UNKNOWN;
	}

	@Override
	public LBool checkSat() {
		m_Cmds.add(new SimpleCmd("check-sat"));
		return LBool.UNKNOWN;
	}

	@Override
	public Term[] getAssertions() throws SMTLIBException {
		m_Cmds.add(new SimpleCmd("get-assertions"));
		return null;
	}

	@Override
	public Term getProof() throws SMTLIBException,
			UnsupportedOperationException {
		m_Cmds.add(new SimpleCmd("get-proof"));
		return null;
	}

	@Override
	public Term[] getUnsatCore() throws SMTLIBException,
			UnsupportedOperationException {
		m_Cmds.add(new SimpleCmd("get-unsat-core"));
		return null;
	}

	@Override
	public Map<Term, Term> getValue(Term[] terms) throws SMTLIBException,
			UnsupportedOperationException {
		m_Cmds.add(new TermListCmd("get-value", terms));
		return null;
	}

	@Override
	public Assignments getAssignment() throws SMTLIBException,
			UnsupportedOperationException {
		m_Cmds.add(new SimpleCmd("get-assignments"));
		return null;
	}

	@Override
	public Object getOption(String opt) throws UnsupportedOperationException {
		m_Cmds.add(new GetterCmd("get-option", opt));
		return null;
	}

	@Override
	public Object getInfo(String info) throws UnsupportedOperationException {
		m_Cmds.add(new GetterCmd("get-info", info));
		return null;
	}

	@Override
	public Term simplify(Term term) throws SMTLIBException {
		m_Cmds.add(new OneTermCmd("simplify", term));
		return null;
	}

	@Override
	public Term[] getInterpolants(Term[] partition, int[] startOfSubtree)
			throws SMTLIBException, UnsupportedOperationException {
		m_Cmds.add(new GetInterpolants(partition, startOfSubtree));
		return null;
	}

	@Override
	public void exit() {
		m_Cmds.add(new SimpleCmd("exit"));
	}

	@Override
	public Model getModel() throws SMTLIBException,
			UnsupportedOperationException {
		m_Cmds.add(new SimpleCmd("exit"));
		return null;
	}

	@Override
	public Iterable<Term[]> checkAllsat(Term[] predicates)
			throws SMTLIBException, UnsupportedOperationException {
		m_Cmds.add(new TermListCmd("check-allsat", predicates));
		return null;
	}
	
}
