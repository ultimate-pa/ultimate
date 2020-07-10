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
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.OutputStream;
import java.io.OutputStreamWriter;
import java.io.PrintWriter;
import java.util.Map;
import java.util.zip.GZIPOutputStream;

/**
 * A logging script variant. This is actually a wrapper around a concrete implementation of the {@link Script} interface
 * that produces an interaction file in (almost) SMTLIB 2 compliant format. We still have some extra commands like
 * "simplify", "reset", or "get-interpolants".
 *
 * @author Juergen Christ
 */
public class LoggingScript extends WrapperScript {

	/**
	 * The interaction log writer.
	 */
	private final PrintWriter mPw;

	/**
	 * The auxiliary class to print terms and sorts.
	 */
	private final PrintTerm mTermPrinter = new PrintTerm();

	/**
	 * Common subexpression elimination support if requeste by user. Will be <code>null</code> if cse should not be
	 * performed.
	 */
	private final FormulaLet mLetter;

	/**
	 * Create a new script logging the commands by the user. Most commands are not supported, e.g., checkSat always
	 * returns unknown. Furthermore, common subexpression elimination is not used in the output.
	 *
	 * @param file
	 *            The name of the logging file (should end in .smt2).
	 * @param autoFlush
	 *            Automatically flush the output stream after every command.
	 * @throws IOException
	 *             IOException If an I/O error has occurred.
	 */
	public LoggingScript(final String file, final boolean autoFlush) throws IOException {
		this(new NoopScript(), file, autoFlush);
	}

	/**
	 * Create a new script logging the commands by the user. Most commands are not supported, e.g., checkSat always
	 * returns unknown. This constructor can be used to set up logging using common subexpression elimination.
	 *
	 * @param file
	 *            The name of the logging file (should end in .smt2).
	 * @param autoFlush
	 *            Automatically flush the output stream after every command.
	 * @param useCSE
	 *            Use common subexpression elimination in output (introduces let terms)
	 * @throws IOException
	 *             IOException If an I/O error has occurred.
	 */
	public LoggingScript(final String file, final boolean autoFlush, final boolean useCSE) throws IOException {
		this(new NoopScript(), file, autoFlush, useCSE);
	}

	/**
	 * Create a new script logging the interaction between the user and the wrapped script into a file. This constructor
	 * sets up logging to not use common subexpression elimination.
	 *
	 * @param script
	 *            The wrapped script.
	 * @param file
	 *            The name of the logging file (should end in .smt2).
	 * @param autoFlush
	 *            Automatically flush the output stream after every command.
	 * @throws IOException
	 *             IOException If an I/O error has occurred.
	 */
	public LoggingScript(final Script script, final String file, final boolean autoFlush) throws IOException {
		this(script, file, autoFlush, false);
	}

	/**
	 * Create a new script logging the interaction between the user and the wrapped script into a file. This constructor
	 * can be used to set up logging using common subexpression elimination.
	 *
	 * @param script
	 *            The wrapped script.
	 * @param file
	 *            The name of the logging file (should end in .smt2).
	 * @param autoFlush
	 *            Automatically flush the output stream after every command.
	 * @param useCSE
	 *            Use common subexpression elimination in output (introduces let terms)
	 * @throws IOException
	 *             IOException If an I/O error has occurred.
	 */
	public LoggingScript(final Script script, final String file, final boolean autoFlush, final boolean useCSE)
			throws IOException {
		super(script);
		OutputStream out;
		if (file.equals("<stdout>")) {
			out = System.out;
		} else if (file.equals("<stderr>")) {
			out = System.err;
		} else {
			out = new FileOutputStream(file);
			if (file.endsWith(".gz")) {
				out = new GZIPOutputStream(out);
			}
		}
		mPw = new PrintWriter(new BufferedWriter(new OutputStreamWriter(out)), autoFlush);
		mLetter = useCSE ? new FormulaLet() : null;
	}

	private final Term formatTerm(final Term input) {
		return mLetter == null ? input : new FormulaLet().let(input);
	}

	@Override
	public void setLogic(final String logic) throws UnsupportedOperationException, SMTLIBException {
		mPw.println("(set-logic " + logic + ")");
		super.setLogic(logic);
	}

	@Override
	public void setLogic(final Logics logic) throws UnsupportedOperationException, SMTLIBException {
		mPw.println("(set-logic " + logic.name() + ")");
		super.setLogic(logic);
	}

	@Override
	public void setOption(final String opt, final Object value) throws UnsupportedOperationException, SMTLIBException {
		mPw.print("(set-option ");
		mPw.print(opt);
		mPw.print(' ');
		mPw.print(PrintTerm.quoteObjectIfString(value));
		mPw.println(")");
		super.setOption(opt, value);
	}

	@Override
	public void setInfo(final String info, final Object value) {
		mPw.print("(set-info ");
		mPw.print(info);
		mPw.print(' ');
		mPw.print(PrintTerm.quoteObjectIfString(value));
		mPw.println(")");
		super.setInfo(info, value);
	}

	@Override
	public FunctionSymbol getFunctionSymbol(final String constructor) {
		return mScript.getFunctionSymbol(constructor);
	}

	@Override
	public void declareSort(final String sort, final int arity) throws SMTLIBException {
		mPw.print("(declare-sort ");
		mPw.print(PrintTerm.quoteIdentifier(sort));
		mPw.print(' ');
		mPw.print(arity);
		mPw.println(")");
		super.declareSort(sort, arity);
	}

	@Override
	public void defineSort(final String sort, final Sort[] sortParams, final Sort definition) throws SMTLIBException {
		mPw.print("(define-sort ");
		mPw.print(PrintTerm.quoteIdentifier(sort));
		mPw.print(" (");
		String sep = "";
		for (final Sort p : sortParams) {
			mPw.print(sep);
			mTermPrinter.append(mPw, p);
			sep = " ";
		}
		mPw.print(") ");
		mTermPrinter.append(mPw, definition);
		mPw.println(")");
		super.defineSort(sort, sortParams, definition);
	}

	@Override
	public void declareDatatype(final DataType datatype, final DataType.Constructor[] constrs) throws SMTLIBException {
		assert datatype.mNumParams == 0;
		mPw.print("(declare-datatype ");
		mPw.print(PrintTerm.quoteIdentifier(datatype.getName()));
		mPw.print(" (");
		for (int j = 0; j < constrs.length; j++) {
			mPw.print("(");
			mPw.print(PrintTerm.quoteIdentifier(constrs[j].getName()));
			for (int k = 0; k < constrs[j].getArgumentSorts().length; k++) {
				mPw.print(" ");
				mPw.print("(");
				mPw.print(PrintTerm.quoteIdentifier(constrs[j].getSelectors()[k]));
				mPw.print(" ");
				mPw.print(constrs[j].getArgumentSorts()[k]);
				mPw.print(")");
			}
			mPw.print(j != constrs.length - 1 ? ") " : ")");
		}
		mPw.println("))");
		super.declareDatatype(datatype, constrs);
	}

	@Override
	public void declareDatatypes(final DataType[] datatypes, final DataType.Constructor[][] constrs,
			final Sort[][] sortParams) throws SMTLIBException {
		assert datatypes.length == constrs.length && datatypes.length == sortParams.length;
		mPw.print("(declare-datatypes (");
		String sep1 = "";
		for (final DataType datatype : datatypes) {
			mPw.print(sep1);
			sep1 = " ";
			mPw.print("(");
			mPw.print(PrintTerm.quoteIdentifier(datatype.getName()));
			mPw.print(" ");
			mPw.print(datatype.mNumParams);
			mPw.print(")");
		}
		mPw.print(") (");
		String sep2 = "";
		for (int i = 0; i < constrs.length; i++) {
			mPw.print(sep2);
			sep2 = " ";
			if (sortParams[i] != null) {
				mPw.print("(par (");
				String sep3 = "";
				for (final Sort param : sortParams[i]) {
					mPw.print(sep3);
					sep3 = " ";
					mPw.print(param);
				}
				mPw.print(") ");
			}
			mPw.print("(");
			String sep4 = "";
			for (final DataType.Constructor constructor : constrs[i]) {
				mPw.print(sep4);
				sep4 = " ";
				mPw.print("(");
				mPw.print(PrintTerm.quoteIdentifier(constructor.getName()));
				for (int j = 0; j < constructor.getArgumentSorts().length; j++) {
					mPw.print(" ");
					mPw.print("(");
					mPw.print(PrintTerm.quoteIdentifier(constructor.getSelectors()[j]));
					mPw.print(" ");
					mPw.print(constructor.getArgumentSorts()[j]);
					mPw.print(")");
				}
				mPw.print(")");
			}
			mPw.print(")");
			if (sortParams[i] != null) {
				mPw.print(")");
			}
		}
		mPw.println("))");
		super.declareDatatypes(datatypes, constrs, sortParams);
	}

	@Override
	public void declareFun(final String fun, final Sort[] paramSorts, final Sort resultSort) throws SMTLIBException {
		mPw.print("(declare-fun ");
		mPw.print(PrintTerm.quoteIdentifier(fun));
		mPw.print(" (");
		String sep = "";
		for (final Sort p : paramSorts) {
			mPw.print(sep);
			mTermPrinter.append(mPw, p);
			sep = " ";
		}
		mPw.print(") ");
		mTermPrinter.append(mPw, resultSort);
		mPw.println(")");
		super.declareFun(fun, paramSorts, resultSort);
	}

	@Override
	public void defineFun(final String fun, final TermVariable[] params, final Sort resultSort, final Term definition)
			throws SMTLIBException {
		mPw.print("(define-fun ");
		mPw.print(PrintTerm.quoteIdentifier(fun));
		mPw.print(" (");
		String sep = "(";
		for (final TermVariable t : params) {
			mPw.print(sep);
			mPw.print(t);
			mPw.print(' ');
			mTermPrinter.append(mPw, t.getSort());
			mPw.print(')');
			sep = " (";
		}
		mPw.print(") ");
		mTermPrinter.append(mPw, resultSort);
		mPw.print(' ');
		mTermPrinter.append(mPw, formatTerm(definition));
		mPw.println(")");
		super.defineFun(fun, params, resultSort, definition);
	}

	@Override
	public void push(final int levels) throws SMTLIBException {
		mPw.println("(push " + levels + ")");
		super.push(levels);
	}

	@Override
	public void pop(final int levels) throws SMTLIBException {
		mPw.println("(pop " + levels + ")");
		super.pop(levels);
	}

	@Override
	public LBool assertTerm(final Term term) throws SMTLIBException {
		mPw.print("(assert ");
		mTermPrinter.append(mPw, formatTerm(term));
		mPw.println(")");
		return super.assertTerm(term);
	}

	@Override
	public LBool checkSat() throws SMTLIBException {
		mPw.println("(check-sat)");
		return super.checkSat();
	}

	@Override
	public LBool checkSatAssuming(final Term... assumptions) throws SMTLIBException {
		mPw.print("(check-sat-assuming (");
		String sep = "";
		for (final Term t : assumptions) {
			mPw.print(sep);
			mTermPrinter.append(mPw, formatTerm(t));
			sep = " ";
		}
		mPw.println("))");
		return super.checkSatAssuming(assumptions);
	}

	@Override
	public Term[] getAssertions() throws SMTLIBException {
		mPw.println("(get-assertions)");
		return super.getAssertions();
	}

	@Override
	public Term getProof() throws SMTLIBException, UnsupportedOperationException {
		mPw.println("(get-proof)");
		return super.getProof();
	}

	@Override
	public Term[] getUnsatCore() throws SMTLIBException, UnsupportedOperationException {
		mPw.println("(get-unsat-core)");
		return super.getUnsatCore();
	}

	@Override
	public Map<Term, Term> getValue(final Term[] terms) throws SMTLIBException, UnsupportedOperationException {
		mPw.print("(get-value (");
		String sep = "";
		for (final Term t : terms) {
			mPw.print(sep);
			mTermPrinter.append(mPw, formatTerm(t));
			sep = " ";
		}
		mPw.println("))");
		return super.getValue(terms);
	}

	@Override
	public Assignments getAssignment() throws SMTLIBException, UnsupportedOperationException {
		mPw.println("(get-assignment)");
		return super.getAssignment();
	}

	@Override
	public Object getOption(final String opt) throws UnsupportedOperationException {
		mPw.println("(get-option " + opt + ")");
		return super.getOption(opt);
	}

	@Override
	public Object getInfo(final String info) throws UnsupportedOperationException {
		mPw.println("(get-info " + info + ")");
		return super.getInfo(info);
	}

	@Override
	public Term simplify(final Term term) throws SMTLIBException {
		mPw.print("(simplify ");
		mTermPrinter.append(mPw, term);
		mPw.println(")");
		return super.simplify(term);
	}

	@Override
	public void reset() {
		mPw.println("(reset)");
		super.reset();
	}

	@Override
	public Term[] getInterpolants(final Term[] partition) throws SMTLIBException, UnsupportedOperationException {
		mPw.print("(get-interpolants");
		for (final Term t : partition) {
			mPw.print(' ');
			mTermPrinter.append(mPw, t);
		}
		mPw.println(')');
		return super.getInterpolants(partition);
	}

	private void printInterpolantQuery(final Term[] partition, final int[] startOfSubtree) {
		// Grammar for tree interpolation:
		// tree ::= children term
		// children ::= tree ('(' tree ')')*
		//
		// So the an open parenthesis marks the beginning of a new sibling.
		// example: parent c, children a, b.
		// partitions: [a,b,c]
		// startofSubtree: [0,1,0]
		// textual representation: a (b) c
		mTermPrinter.append(mPw, partition[0]);
		for (int i = 1; i < partition.length; ++i) {
			int prevStart = startOfSubtree[i - 1];
			while (startOfSubtree[i] < prevStart) {
				mPw.print(')');
				prevStart = startOfSubtree[prevStart - 1];
			}
			mPw.print(' ');
			if (startOfSubtree[i] == i) {
				mPw.print('(');
			}
			mTermPrinter.append(mPw, partition[i]);
		}
	}

	@Override
	public Term[] getInterpolants(final Term[] partition, final int[] startOfSubtree)
			throws SMTLIBException, UnsupportedOperationException {
		mPw.print("(get-interpolants ");
		printInterpolantQuery(partition, startOfSubtree);
		mPw.println(')');
		return super.getInterpolants(partition, startOfSubtree);
	}

	@Override
	public Term[] getInterpolants(final Term[] partition, final int[] startOfSubtree, final Term proofTree)
			throws SMTLIBException, UnsupportedOperationException {
		mPw.print("(get-interpolants ");
		printInterpolantQuery(partition, startOfSubtree);
		mPw.print(" :proof ");
		mTermPrinter.append(mPw, proofTree);
		mPw.println(')');
		return super.getInterpolants(partition, startOfSubtree);
	}

	@Override
	public void exit() {
		mPw.println("(exit)");
		mPw.flush();
		mPw.close();
		super.exit();
	}

	@Override
	public Model getModel() throws SMTLIBException, UnsupportedOperationException {
		mPw.println("(get-model)");
		return super.getModel();
	}

	@Override
	public Iterable<Term[]> checkAllsat(final Term[] predicates) throws SMTLIBException, UnsupportedOperationException {
		final PrintTerm pt = new PrintTerm();
		mPw.print("(check-allsat (");
		String spacer = "";
		for (final Term p : predicates) {
			mPw.print(spacer);
			pt.append(mPw, p);
			spacer = " ";
		}
		mPw.println("))");
		return super.checkAllsat(predicates);
	}

	@Override
	public Term[] findImpliedEquality(final Term[] x, final Term[] y) {
		final PrintTerm pt = new PrintTerm();
		mPw.print("(find-implied-equality (");
		String spacer = "";
		for (final Term p : x) {
			mPw.print(spacer);
			pt.append(mPw, p);
			spacer = " ";
		}
		mPw.print(") (");
		spacer = "";
		for (final Term p : x) {
			mPw.print(spacer);
			pt.append(mPw, p);
			spacer = " ";
		}
		mPw.println("))");
		return super.findImpliedEquality(x, y);
	}

	@Override
	public QuotedObject echo(final QuotedObject msg) {
		mPw.print("(echo ");
		mPw.print(msg);
		mPw.println(')');
		return super.echo(msg);
	}

	/**
	 * Write a comment to the generated SMTLIB dump file. Note that this function is only available in the LoggingScript
	 * and not in the interface {@link Script} since it only makes sense for logging and not for solving.
	 *
	 * @param comment
	 *            The comment to write to the dump file.
	 */
	public void comment(final String comment) {
		mPw.print("; ");
		mPw.println(comment);
	}

	@Override
	public void resetAssertions() {
		mPw.println("(reset-assertions)");
		super.resetAssertions();
	}

	@Override
	public Term[] getUnsatAssumptions() throws SMTLIBException, UnsupportedOperationException {
		mPw.println("(get-unsat-assumptions)");
		return super.getUnsatAssumptions();
	}
}
