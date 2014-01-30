/*
 * Copyright (C) 2009-2012 University of Freiburg
 *
 * This file is part of SMTInterpol.
 *
 * SMTInterpol is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * SMTInterpol is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with SMTInterpol.  If not, see <http://www.gnu.org/licenses/>.
 */
package de.uni_freiburg.informatik.ultimate.logic;

import java.io.BufferedWriter;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.OutputStream;
import java.io.OutputStreamWriter;
import java.io.PrintWriter;
import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.Map;

/**
 * A logging script variant.  This is actually a wrapper around a concrete
 * implementation of the {@link Script} interface that produces an interaction
 * file in (almost) SMTLIB 2 compliant format.  We still have some extra
 * commands like "simplify", "reset", or "get-interpolants".
 * @author Juergen Christ
 */
public class LoggingScript implements Script {

	/**
	 * The actual script.
	 */
	private Script m_Script;
	/**
	 * The interaction log writer.
	 */
	private PrintWriter m_Pw;

	/**
	 * The auxiliary class to print terms and sorts.
	 */
	private PrintTerm m_TermPrinter = new PrintTerm();
	
	/**
	 * Create a new script logging the commands by the user.  Most commands
	 * are not supported, e.g., checkSat always returns unknown.
	 * @param file      The name of the logging file (should end in .smt2).
	 * @param autoFlush Automatically flush the output stream after every command.
	 * @throws FileNotFoundException If the file cannot be opened.
	 */
	public LoggingScript(String file, boolean autoFlush) throws FileNotFoundException {
		this (new NoopScript(), file, autoFlush);
	}
	
	/**
	 * Create a new script logging the interaction between the user and the
	 * wrapped script into a file.
	 * @param script    The wrapped script.
	 * @param file      The name of the logging file (should end in .smt2).
	 * @param autoFlush Automatically flush the output stream after every command.
	 * @throws FileNotFoundException If the file cannot be opened.
	 */
	public LoggingScript(Script script, String file, boolean autoFlush)
	throws FileNotFoundException {
		m_Script = script;
		OutputStream out;
		if (file.equals("<stdout>"))
			out = System.out;
		else if (file.equals("<stderr>"))
			out = System.err;
		else
			out = new FileOutputStream(file);
		m_Pw = new PrintWriter(new BufferedWriter(new OutputStreamWriter(out)), autoFlush);
	}
	
	@Override
	public void setLogic(String logic)
	throws UnsupportedOperationException, SMTLIBException {
		m_Pw.println("(set-logic " + logic + ")");
		m_Script.setLogic(logic);
	}
	
	@Override
	public void setLogic(Logics logic)
	throws UnsupportedOperationException, SMTLIBException {
		m_Pw.println("(set-logic " + logic.name() + ")");
		m_Script.setLogic(logic);
	}

	@Override
	public void setOption(String opt, Object value)
			throws UnsupportedOperationException, SMTLIBException {
		m_Pw.print("(set-option ");
		m_Pw.print(opt);
		m_Pw.print(' ');
		m_Pw.print(value);
		m_Pw.println(")");
		m_Script.setOption(opt, value);
	}

	@Override
	public void setInfo(String info, Object value) {
		m_Pw.print("(set-info ");
		m_Pw.print(info);
		m_Pw.print(' ');
		m_Pw.print(value);
		m_Pw.println(")");
		m_Script.setInfo(info, value);
	}

	@Override
	public void declareSort(String sort, int arity) throws SMTLIBException {
		m_Pw.print("(declare-sort ");
		m_Pw.print(PrintTerm.quoteIdentifier(sort));
		m_Pw.print(' ');
		m_Pw.print(arity);
		m_Pw.println(")");
		m_Script.declareSort(sort, arity);
	}

	@Override
	public void defineSort(String sort, Sort[] sortParams, Sort definition)
			throws SMTLIBException {
		m_Pw.print("(define-sort ");
		m_Pw.print(PrintTerm.quoteIdentifier(sort));
		m_Pw.print(" (");
		String sep = "";
		for (Sort p : sortParams) {
			m_Pw.print(sep);
			m_TermPrinter.append(m_Pw, p);
			sep = " ";
		}
		m_Pw.print(") ");
		m_TermPrinter.append(m_Pw, definition);
		m_Pw.println(")");
		m_Script.defineSort(sort, sortParams, definition);
	}

	@Override
	public void declareFun(String fun, Sort[] paramSorts, Sort resultSort)
			throws SMTLIBException {
		m_Pw.print("(declare-fun ");
		m_Pw.print(PrintTerm.quoteIdentifier(fun));
		m_Pw.print(" (");
		String sep = "";
		for (Sort p : paramSorts) {
			m_Pw.print(sep);
			m_TermPrinter.append(m_Pw, p);
			sep = " ";
		}
		m_Pw.print(") ");
		m_TermPrinter.append(m_Pw, resultSort);
		m_Pw.println(")");
		m_Script.declareFun(fun, paramSorts, resultSort);
	}

	@Override
	public void defineFun(String fun, TermVariable[] params, Sort resultSort,
			Term definition) throws SMTLIBException {
		m_Pw.print("(define-fun ");
		m_Pw.print(PrintTerm.quoteIdentifier(fun));
		m_Pw.print(" (");
		String sep = "(";
		for (TermVariable t : params) {
			m_Pw.print(sep);
			m_Pw.print(t);
			m_Pw.print(' ');
			m_TermPrinter.append(m_Pw, t.getSort());
			m_Pw.print(')');
			sep = " (";
		}
		m_Pw.print(") ");
		m_TermPrinter.append(m_Pw, resultSort);
		m_Pw.print(' ');
		m_TermPrinter.append(m_Pw, definition);
		m_Pw.println(")");
		m_Script.defineFun(fun, params, resultSort, definition);
	}

	@Override
	public void push(int levels) throws SMTLIBException {
		m_Pw.println("(push " + levels + ")");
		m_Script.push(levels);
	}

	@Override
	public void pop(int levels) throws SMTLIBException {
		m_Pw.println("(pop " + levels + ")");
		m_Script.pop(levels);
	}

	@Override
	public LBool assertTerm(Term term) throws SMTLIBException {
		m_Pw.print("(assert ");
		m_TermPrinter.append(m_Pw, term);
		m_Pw.println(")");
		return m_Script.assertTerm(term);
	}

	@Override
	public LBool checkSat() throws SMTLIBException {
		m_Pw.println("(check-sat)");
		return m_Script.checkSat();
	}

	@Override
	public Term[] getAssertions() throws SMTLIBException {
		m_Pw.println("(get-assertions)");
		return m_Script.getAssertions();
	}

	@Override
	public Term getProof() throws SMTLIBException,
			UnsupportedOperationException {
		m_Pw.println("(get-proof)");
		return m_Script.getProof();
	}

	@Override
	public Term[] getUnsatCore() throws SMTLIBException,
			UnsupportedOperationException {
		m_Pw.println("(get-unsat-core)");
		return m_Script.getUnsatCore();
	}

	@Override
	public Map<Term, Term> getValue(Term[] terms) throws SMTLIBException,
			UnsupportedOperationException {
		m_Pw.print("(get-value (");
		String sep = "";
		for (Term t : terms) {
			m_Pw.print(sep);
			m_TermPrinter.append(m_Pw, t);
			sep = " ";
		}
		m_Pw.println("))");
		return m_Script.getValue(terms);
	}

	@Override
	public Assignments getAssignment() throws SMTLIBException,
			UnsupportedOperationException {
		m_Pw.println("(get-assignment)");
		return m_Script.getAssignment();
	}

	@Override
	public Object getOption(String opt) throws UnsupportedOperationException {
		m_Pw.println("(get-option " + opt + ")");
		return m_Script.getOption(opt);
	}

	@Override
	public Object getInfo(String info) throws UnsupportedOperationException {
		m_Pw.println("(get-info " + info + ")");
		return m_Script.getInfo(info);
	}

	@Override
	public Term simplify(Term term) throws SMTLIBException {
		m_Pw.print("(simplify ");
		m_TermPrinter.append(m_Pw, term);
		m_Pw.println(")");
		return m_Script.simplify(term);
	}

	@Override
	public void reset() {
		m_Pw.println("(reset)");
		m_Script.reset();
	}

	@Override
	public Term[] getInterpolants(Term[] partition) throws SMTLIBException,
			UnsupportedOperationException {
		m_Pw.print("(get-interpolants");
		for (Term t : partition) {
			m_Pw.print(' ');
			m_TermPrinter.append(m_Pw, t);
		}
		m_Pw.println(')');
		return m_Script.getInterpolants(partition);
	}
	
	// [a,b,c], [0,1,0] -> a (b) c
	//  c
	// a b
	@Override
	public Term[] getInterpolants(Term[] partition, int[] startOfSubtree)
	throws SMTLIBException,	UnsupportedOperationException {
		m_Pw.print("(get-interpolants ");
		m_TermPrinter.append(m_Pw, partition[0]);
		for (int i = 1; i < partition.length; ++i) {
			int prevStart = startOfSubtree[i - 1];
			while (startOfSubtree[i] < prevStart) {
				m_Pw.print(')');
				prevStart = startOfSubtree[prevStart - 1];
			}
			m_Pw.print(' ');
			if (startOfSubtree[i] == i)
				m_Pw.print('(');
			m_TermPrinter.append(m_Pw, partition[i]);
		}
		m_Pw.println(')');
		return m_Script.getInterpolants(partition, startOfSubtree);
	}

	@Override
	public void exit() {
		m_Pw.println("(exit)");
		m_Pw.flush();
		m_Pw.close();
		m_Script.exit();
	}

	@Override
	public Sort sort(String sortname, Sort... params) throws SMTLIBException {
		return m_Script.sort(sortname, params);
	}

	@Override
	public Sort sort(String sortname, BigInteger[] indices, Sort... params)
			throws SMTLIBException {
		return m_Script.sort(sortname, indices, params);
	}

	@Override
	public Term term(String funcname, Term... params) throws SMTLIBException {
		return m_Script.term(funcname, params);
	}

	@Override
	public Term term(String funcname, BigInteger[] indices, Sort returnSort,
			Term... params) throws SMTLIBException {
		return m_Script.term(funcname, indices, returnSort, params);
	}

	@Override
	public TermVariable variable(String varname, Sort sort)
			throws SMTLIBException {
		return m_Script.variable(varname, sort);
	}

	@Override
	public Term quantifier(int quantor, TermVariable[] vars, Term body,
			Term[]... patterns) throws SMTLIBException {
		return m_Script.quantifier(quantor, vars, body, patterns);
	}

	@Override
	public Term let(TermVariable[] vars, Term[] values, Term body)
			throws SMTLIBException {
		return m_Script.let(vars, values, body);
	}

	@Override
	public Term annotate(Term t, Annotation... annotations)
			throws SMTLIBException {
		return m_Script.annotate(t, annotations);
	}

	@Override
	public Term numeral(String num) throws SMTLIBException {
		return m_Script.numeral(num);
	}

	@Override
	public Term numeral(BigInteger num) throws SMTLIBException {
		return m_Script.numeral(num);
	}

	@Override
	public Term decimal(String decimal) throws SMTLIBException {
		return m_Script.decimal(decimal);
	}

	@Override
	public Term decimal(BigDecimal decimal) throws SMTLIBException {
		return m_Script.decimal(decimal);
	}

	@Override
	public Term string(String str) throws SMTLIBException {
		return m_Script.string(str);
	}

	@Override
	public Term hexadecimal(String hex) throws SMTLIBException {
		return m_Script.hexadecimal(hex);
	}

	@Override
	public Term binary(String bin) throws SMTLIBException {
		return m_Script.binary(bin);
	}

	@Override
	public Sort[] sortVariables(String... names) throws SMTLIBException {
		return m_Script.sortVariables(names);
	}

	@Override
	public Model getModel() throws SMTLIBException,
			UnsupportedOperationException {
		m_Pw.println("(get-model)");
		return m_Script.getModel();
	}

	@Override
	public Iterable<Term[]> checkAllsat(Term[] predicates) throws SMTLIBException,
			UnsupportedOperationException {
		PrintTerm pt = new PrintTerm();
		m_Pw.print("(check-allsat (");
		String spacer = "";
		for (Term p : predicates) {
			m_Pw.print(spacer);
			pt.append(m_Pw, p);
			spacer = " ";
		}
		m_Pw.println("))");
		return m_Script.checkAllsat(predicates);
	}

	@Override
	public Term[] findImpliedEquality(Term[] x, Term[] y) {
		PrintTerm pt = new PrintTerm();
		m_Pw.print("(find-implied-equality (");
		String spacer = "";
		for (Term p : x) {
			m_Pw.print(spacer);
			pt.append(m_Pw, p);
			spacer = " ";
		}
		m_Pw.print(") (");
		spacer = "";
		for (Term p : x) {
			m_Pw.print(spacer);
			pt.append(m_Pw, p);
			spacer = " ";
		}
		m_Pw.println("))");
		return m_Script.findImpliedEquality(x, y);
	}
}
