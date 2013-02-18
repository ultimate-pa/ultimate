package de.uni_freiburg.informatik.ultimate.smtsolver.external;


import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.logic.Assignments;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.Model;
import de.uni_freiburg.informatik.ultimate.logic.NoopScript;
import de.uni_freiburg.informatik.ultimate.logic.PrintTerm;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Valuation;

/**
 * Create a script that connects to an external SMT solver.  The solver 
 * must be SMTLIB-2 compliant and expect commands on standard input. It
 * must return its output on standard output. 
 * 
 * Some commands are only partially supported.  For example getProof does
 * not return a useful proof object.  Also commands, for which the output
 * format is not fully specified, e.g. (get-model), may not return useful
 * return values.
 * 
 * @author Oday Jubran
 */
public class Scriptor extends NoopScript {
	
	private Executor m_Executor;
	private LBool m_Status = LBool.UNKNOWN;
	
	/**
	 * Create a script connecting to an external SMT solver.
	 * @param command the command that starts the external SMT solver.
	 *   The solver is expected to read smtlib 2 commands on stdin.
	 */
	public Scriptor(String command, Logger logger)
	{
		m_Executor = new Executor(command, this, logger);
		super.setOption(":print-success", true);
	}
	
	@Override
	public void setLogic(String logic) throws UnsupportedOperationException,
			SMTLIBException {
		super.setLogic(logic);
		m_Executor.input("(set-logic " + logic + ")");
		m_Executor.parseSuccess();
	}

	@Override
	public void setLogic(Logics logic) throws UnsupportedOperationException,
			SMTLIBException {
		super.setLogic(logic);
		m_Executor.input("(set-logic " + logic + ")");
		m_Executor.parseSuccess();
	}

	@Override
	public void setOption(String opt, Object value)
			throws UnsupportedOperationException, SMTLIBException {
		if (!opt.equals(":print-success")) {
			StringBuilder sb = new StringBuilder();
			sb.append("(set-option ").append(opt);
			if (value != null) {
				sb.append(" ");
				if (value instanceof String) {
					// symbol
					sb.append(PrintTerm.quoteIdentifier((String) value));
				} else if (value instanceof Object[]) {
					// s-expr
					new PrintTerm().append(sb, (Object[]) value);
				} else {
					sb.append(value.toString());
				}
			}
			sb.append(")");
			m_Executor.input(sb.toString());		
			m_Executor.parseSuccess();
		}
	}

	@Override
	public void setInfo(String info, Object value) {
		StringBuilder sb = new StringBuilder();
		sb.append("(set-info ").append(info);
		if (value != null) {
			sb.append(" ");
			if (value instanceof String) {
				// symbol
				sb.append(PrintTerm.quoteIdentifier((String) value));
			} else if (value instanceof Object[]) {
				// s-expr
				new PrintTerm().append(sb, (Object[]) value);
			} else {
				sb.append(value.toString());
			}
		}
		sb.append(")");
		m_Executor.input(sb.toString());		
		m_Executor.parseSuccess();
	}

	@Override
	public void declareSort(String sort, int arity) throws SMTLIBException {
		super.declareSort(sort, arity);
		StringBuilder sb = new StringBuilder("(declare-sort ").append
				(PrintTerm.quoteIdentifier(sort));
		sb.append(" ").append(arity).append(")");
		m_Executor.input(sb.toString());		
		m_Executor.parseSuccess();
	}

	@Override
	public void defineSort(String sort, Sort[] sortParams, Sort definition)
			throws SMTLIBException {
		super.defineSort(sort, sortParams, definition);	
		PrintTerm pt = new PrintTerm();
		StringBuilder sb = new StringBuilder();
		sb.append("(define-sort ");
		sb.append(PrintTerm.quoteIdentifier(sort));
		sb.append(" (");
		String delim = "";
		for (Sort s : sortParams) {
			sb.append(delim);
			pt.append(sb, s);
			delim = " ";
		}
		sb.append(") ");
		pt.append(sb, definition);
		sb.append(")");
		m_Executor.input(sb.toString());
		m_Executor.parseSuccess();
	}

	@Override
	public void declareFun(String fun, Sort[] paramSorts, Sort resultSort)
			throws SMTLIBException {
		super.declareFun(fun, paramSorts, resultSort);
		PrintTerm pt = new PrintTerm();
		StringBuilder sb = new StringBuilder();
		sb.append("(declare-fun ");
		sb.append(PrintTerm.quoteIdentifier(fun));
		sb.append(" (");
		String delim = "";
		for (Sort s : paramSorts) {
			sb.append(delim);
			pt.append(sb, s);
			delim = " ";
		}
		sb.append(") ");
		pt.append(sb, resultSort);
		sb.append(")");
		m_Executor.input(sb.toString());
		m_Executor.parseSuccess();
	}

	@Override
	public void defineFun(String fun, TermVariable[] params, Sort resultSort,
			Term definition) throws SMTLIBException {
		super.defineFun(fun, params, resultSort, definition);
		PrintTerm pt = new PrintTerm();
		StringBuilder sb = new StringBuilder();
		sb.append("(define-fun ");
		sb.append(PrintTerm.quoteIdentifier(fun));
		sb.append(" (");
		String delim = "";
		for (TermVariable t : params) {
			sb.append(delim);
			sb.append("(").append(t).append(" ");
			pt.append(sb, t.getSort());
			sb.append(")");
			delim = " ";
		}
		sb.append(") ");
		pt.append(sb, resultSort);
		pt.append(sb, definition);
		sb.append(")");
		m_Executor.input(sb.toString());
		m_Executor.parseSuccess();
	}

	@Override
	public void push(int levels) throws SMTLIBException {
		super.push(levels);
		m_Executor.input("(push "+levels+")");
		m_Executor.parseSuccess();
	}

	@Override
	public void pop(int levels) throws SMTLIBException {
		super.pop(levels);
		m_Executor.input("(pop "+levels+")");
		m_Executor.parseSuccess();
	}

	@Override
	public LBool assertTerm(Term term) throws SMTLIBException {
		//super.assertTerm(term);
		m_Executor.input("(assert " + term.toStringDirect() + ")");
		m_Executor.parseSuccess();
		return LBool.UNKNOWN;
	}

	@Override
	public LBool checkSat() throws SMTLIBException {
		m_Executor.input("(check-sat)");
		m_Status = m_Executor.parseCheckSatResult();
		return m_Status;
	}

	@Override
	public Term[] getAssertions() throws SMTLIBException {
		m_Executor.input("(get-assertions)");
		return m_Executor.parseGetAssertionsResult();
	}

	/** Proofs are not supported, since they are not standardized **/
	@Override
	public Term getProof() throws SMTLIBException,
			UnsupportedOperationException {
		throw new UnsupportedOperationException("Proofs are not supported");
	}

	@Override
	public Term[] getUnsatCore() throws SMTLIBException,
			UnsupportedOperationException {
		m_Executor.input("(get-unsat-core)");
		return m_Executor.parseGetUnsatCoreResult();
	}

	@Override
	public Valuation getValue(Term[] terms) throws SMTLIBException,
			UnsupportedOperationException {
		for (Term t : terms) {
			if (!t.getSort().isNumericSort() &&
				t.getSort() != getTheory().getBooleanSort())
				throw new UnsupportedOperationException();
		}
		StringBuilder command = new StringBuilder();
		PrintTerm pt = new PrintTerm();
		command.append("(get-value (");
		String sep = "";
		for (Term t : terms) {
			command.append(sep);
			pt.append(command, t);
			sep = " ";
		}
		command.append("))");
		m_Executor.input(command.toString());
		return m_Executor.parseGetValueResult();
	}

	@Override
	public Assignments getAssignment() throws SMTLIBException,
			UnsupportedOperationException {
		m_Executor.input("(get-assignment)");
		return m_Executor.parseGetAssignmentResult();
	}

	@Override
	public Object getOption(String opt) throws UnsupportedOperationException {
		m_Executor.input("(get-option " + opt + ")");
		return m_Executor.parseGetOptionResult();
	}

	@Override
	public Object getInfo(String info) throws UnsupportedOperationException {
		m_Executor.input("(get-info " + info + ")");
		Object[] result = m_Executor.parseGetInfoResult();
		if (result.length == 1)
			return result[0];
		return result;
	}

	@Override
	public void exit() {
		m_Executor.input("(exit)");
		m_Executor.parseSuccess();
		
		
	}

	@Override
	public Term simplifyTerm(Term term) throws SMTLIBException {
		throw new UnsupportedOperationException();
	}

	@Override
	public void reset() {
		super.reset();
		m_Executor.reset();
	}

	@Override
	public Model getModel() throws SMTLIBException,
			UnsupportedOperationException {
		throw new UnsupportedOperationException();
	}
	
	/** This method is used in the output parser, to support (get-info :status) **/
	public LBool getStatus() {
		return m_Status;
	}
}
