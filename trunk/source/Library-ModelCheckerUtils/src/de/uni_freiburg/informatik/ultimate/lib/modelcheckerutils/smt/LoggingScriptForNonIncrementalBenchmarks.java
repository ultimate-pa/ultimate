/*
 * Copyright (C) 2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 University of Freiburg
 *
 * This file is part of the ULTIMATE ModelCheckerUtils Library.
 *
 * The ULTIMATE ModelCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE ModelCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ModelCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ModelCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE ModelCheckerUtils Library grant you additional permission
 * to convey the resulting work.
 */
/*
 * Copyright (C) 2009-2015 University of Freiburg
 *
 * This file is part of the ULTIMATE ModelCheckerUtils Library.
 *
 * The ULTIMATE ModelCheckerUtils Library is free software: you can redistribute
 * it and/or modify it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation, either version 3 of the
 * License, or (at your option) any later version.
 *
 * The ULTIMATE ModelCheckerUtils Library is distributed in the hope that it
 * will be useful, but WITHOUT ANY WARRANTY; without even the implied warranty
 * of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Automata Library.  If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Automata Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE ModelCheckerUtils Library grant you additional
 * permission to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt;

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintWriter;
import java.io.StringWriter;
import java.util.ArrayList;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.logic.Assignments;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.Model;
import de.uni_freiburg.informatik.ultimate.logic.PrintTerm;
import de.uni_freiburg.informatik.ultimate.logic.QuotedObject;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.WrapperScript;
import de.uni_freiburg.informatik.ultimate.smtsolver.external.SmtCommandUtils.AssertCommand;
import de.uni_freiburg.informatik.ultimate.smtsolver.external.SmtCommandUtils.CheckSatCommand;
import de.uni_freiburg.informatik.ultimate.smtsolver.external.SmtCommandUtils.DeclareFunCommand;
import de.uni_freiburg.informatik.ultimate.smtsolver.external.SmtCommandUtils.DeclareSortCommand;
import de.uni_freiburg.informatik.ultimate.smtsolver.external.SmtCommandUtils.DefineFunCommand;
import de.uni_freiburg.informatik.ultimate.smtsolver.external.SmtCommandUtils.DefineSortCommand;
import de.uni_freiburg.informatik.ultimate.smtsolver.external.SmtCommandUtils.EchoCommand;
import de.uni_freiburg.informatik.ultimate.smtsolver.external.SmtCommandUtils.GetUnsatCoreCommand;
import de.uni_freiburg.informatik.ultimate.smtsolver.external.SmtCommandUtils.GetValueCommand;
import de.uni_freiburg.informatik.ultimate.smtsolver.external.SmtCommandUtils.ISmtCommand;
import de.uni_freiburg.informatik.ultimate.smtsolver.external.SmtCommandUtils.SetLogicCommand;
import de.uni_freiburg.informatik.ultimate.smtsolver.external.SmtCommandUtils.SetOptionCommand;

/**
 * This is a wrapper around a {@link Script} that is used by Matthias in order to generate benchmarks for the SMT-COMP
 * 2015. This class contains a lot of code duplication from Jürgen's Logging script. This class is a hack and should be
 * used with extreme caution.
 *
 * @author Matthias Heizmann
 */
public class LoggingScriptForNonIncrementalBenchmarks extends WrapperScript {

	/**
	 * The auxiliary class to print terms and sorts.
	 */
	private final PrintTerm mTermPrinter = new PrintTerm();

	private final String mBaseFilename;
	private final String mDirectory;

	protected final LinkedList<ArrayList<ISmtCommand<?>>> mCommandStack;

	public LoggingScriptForNonIncrementalBenchmarks(final Script script, final String baseFilename,
			final String directory) {
		super(script);
		mBaseFilename = baseFilename;
		mDirectory = directory;
		mCommandStack = new LinkedList<>();
		mCommandStack.push(new ArrayList<ISmtCommand<?>>());
	}

	protected LinkedList<ArrayList<ISmtCommand<?>>> deepCopyOfCommandStack() {
		final LinkedList<ArrayList<ISmtCommand<?>>> result = new LinkedList<>();
		for (final ArrayList<ISmtCommand<?>> al : mCommandStack) {
			result.add(new ArrayList<ISmtCommand<?>>());
			for (final ISmtCommand<?> command : al) {
				result.getLast().add(command);
			}
		}
		return result;
	}

	protected void addToCurrentAssertionStack(final ISmtCommand<?> smtCommand) {
		mCommandStack.getLast().add(smtCommand);
	}

	private void resetAssertionStack() {
		mCommandStack.clear();
		mCommandStack.add(new ArrayList<>());
	}

	private static void printCommandStack(final PrintWriter pw, final List<ArrayList<ISmtCommand<?>>> commandStack) {
		for (final ArrayList<ISmtCommand<?>> al : commandStack) {
			for (final ISmtCommand<?> command : al) {
				pw.print(command.toString() + System.lineSeparator());
			}
		}
	}

	protected void writeCommandStackToFile(final File file, final List<ArrayList<ISmtCommand<?>>> commandStack) {
		FileWriter fw = null;
		try {
			fw = new FileWriter(file);
		} catch (final IOException e) {
			throw new AssertionError("Unable to write file " + file.getAbsolutePath());
		}
		final PrintWriter pw = new PrintWriter(fw);
		printCommandStack(pw, commandStack);
		pw.close();
	}

	protected File constructFile(final String suffix) {
		final String filename = mDirectory + File.separator + mBaseFilename + suffix + ".smt2";
		final File file = new File(filename);
		return file;
	}

	private final static Term formatTerm(final Term input) {
		// return mLetter == null ? input : new FormulaLet().let(input);
		return input;
	}

	@Override
	public void setLogic(final String logic) throws UnsupportedOperationException, SMTLIBException {
		final StringWriter sw = new StringWriter();
		final PrintWriter mPw = new PrintWriter(sw);
		mPw.println("(set-logic " + logic + ")");
		addToCurrentAssertionStack(new SetLogicCommand(logic));
		mScript.setLogic(logic);
	}

	@Override
	public void setLogic(final Logics logic) throws UnsupportedOperationException, SMTLIBException {
		final StringWriter sw = new StringWriter();
		final PrintWriter mPw = new PrintWriter(sw);
		mPw.println("(set-logic " + logic.name() + ")");
		addToCurrentAssertionStack(new SetLogicCommand(logic.name()));
		mScript.setLogic(logic);
	}

	@Override
	public void setOption(final String opt, final Object value) throws UnsupportedOperationException, SMTLIBException {
		final StringWriter sw = new StringWriter();
		final PrintWriter mPw = new PrintWriter(sw);
		mPw.print("(set-option ");
		mPw.print(opt);
		mPw.print(' ');
		mPw.print(PrintTerm.quoteObjectIfString(value));
		mPw.println(")");
		addToCurrentAssertionStack(new SetOptionCommand(opt, value));
		mScript.setOption(opt, value);
	}

	@Override
	public void setInfo(final String info, final Object value) {
		final StringWriter sw = new StringWriter();
		final PrintWriter mPw = new PrintWriter(sw);
		mPw.print("(set-info ");
		mPw.print(info);
		mPw.print(' ');
		mPw.print(PrintTerm.quoteObjectIfString(value));
		mPw.println(")");
		addToCurrentAssertionStack(new SetOptionCommand(info, value));
		mScript.setInfo(info, value);
	}

	@Override
	public void declareSort(final String sort, final int arity) throws SMTLIBException {
		final StringWriter sw = new StringWriter();
		final PrintWriter mPw = new PrintWriter(sw);
		mPw.print("(declare-sort ");
		mPw.print(PrintTerm.quoteIdentifier(sort));
		mPw.print(' ');
		mPw.print(arity);
		mPw.println(")");
		addToCurrentAssertionStack(new DeclareSortCommand(sort, arity));
		mScript.declareSort(sort, arity);
	}

	@Override
	public void defineSort(final String sort, final Sort[] sortParams, final Sort definition) throws SMTLIBException {
		final StringWriter sw = new StringWriter();
		final PrintWriter mPw = new PrintWriter(sw);
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
		addToCurrentAssertionStack(new DefineSortCommand(sort, sortParams, definition));
		mScript.defineSort(sort, sortParams, definition);
	}

	@Override
	public void declareFun(final String fun, final Sort[] paramSorts, final Sort resultSort) throws SMTLIBException {
		final StringWriter sw = new StringWriter();
		final PrintWriter mPw = new PrintWriter(sw);
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
		addToCurrentAssertionStack(new DeclareFunCommand(fun, paramSorts, resultSort));
		mScript.declareFun(fun, paramSorts, resultSort);
	}

	@Override
	public void defineFun(final String fun, final TermVariable[] params, final Sort resultSort, final Term definition)
			throws SMTLIBException {
		final StringWriter sw = new StringWriter();
		final PrintWriter mPw = new PrintWriter(sw);
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
		addToCurrentAssertionStack(new DefineFunCommand(fun, params, resultSort, definition));
		mScript.defineFun(fun, params, resultSort, definition);
	}

	@Override
	public void push(final int levels) throws SMTLIBException {
		// StringWriter sw = new StringWriter();
		// PrintWriter mPw = new PrintWriter(sw);
		// mPw.println("(push " + levels + ")");
		// addToCurrentAssertionStack(sw.toString());
		for (int i = 0; i < levels; i++) {
			mCommandStack.add(new ArrayList<ISmtCommand<?>>());
		}
		mScript.push(levels);
	}

	@Override
	public void pop(final int levels) throws SMTLIBException {
		// StringWriter sw = new StringWriter();
		// PrintWriter mPw = new PrintWriter(sw);
		// mPw.println("(pop " + levels + ")");
		// addToCurrentAssertionStack(sw.toString());
		for (int i = 0; i < levels; i++) {
			mCommandStack.removeLast();
		}
		mScript.pop(levels);
	}

	@Override
	public LBool assertTerm(final Term term) throws SMTLIBException {

		addToCurrentAssertionStack(new AssertCommand(term));
		return mScript.assertTerm(term);
	}

	@Override
	public LBool checkSat() throws SMTLIBException {
		final StringWriter sw = new StringWriter();
		final PrintWriter mPw = new PrintWriter(sw);
		mPw.println("(check-sat)");
		addToCurrentAssertionStack(new CheckSatCommand());
		return mScript.checkSat();
	}

	@Override
	public Term[] getAssertions() throws SMTLIBException {
		final StringWriter sw = new StringWriter();
		final PrintWriter mPw = new PrintWriter(sw);
		mPw.println("(get-assertions)");
		final String commandName = "get-assertions";
		System.out.println("Logging script will ignore the " + commandName + " command.");
		return mScript.getAssertions();
	}

	@Override
	public Term getProof() throws SMTLIBException, UnsupportedOperationException {
		final StringWriter sw = new StringWriter();
		final PrintWriter mPw = new PrintWriter(sw);
		mPw.println("(get-proof)");
		final String commandName = "get-proof";
		System.out.println("Logging script will ignore the " + commandName + " command.");
		return mScript.getProof();
	}

	@Override
	public Term[] getUnsatCore() throws SMTLIBException, UnsupportedOperationException {
		final StringWriter sw = new StringWriter();
		final PrintWriter mPw = new PrintWriter(sw);
		mPw.println("(get-unsat-core)");
		addToCurrentAssertionStack(new GetUnsatCoreCommand());
		return mScript.getUnsatCore();
	}

	@Override
	public Map<Term, Term> getValue(final Term[] terms) throws SMTLIBException, UnsupportedOperationException {
		final StringWriter sw = new StringWriter();
		final PrintWriter mPw = new PrintWriter(sw);
		mPw.print("(get-value (");
		String sep = "";
		for (final Term t : terms) {
			mPw.print(sep);
			mTermPrinter.append(mPw, formatTerm(t));
			sep = " ";
		}
		mPw.println("))");
		addToCurrentAssertionStack(new GetValueCommand(terms));
		return mScript.getValue(terms);
	}

	@Override
	public Assignments getAssignment() throws SMTLIBException, UnsupportedOperationException {
		final StringWriter sw = new StringWriter();
		final PrintWriter mPw = new PrintWriter(sw);
		mPw.println("(get-assignment)");
		final String commandName = "get-assignment";
		System.out.println("Logging script will ignore the " + commandName + " command.");
		return mScript.getAssignment();
	}

	@Override
	public Object getOption(final String opt) throws UnsupportedOperationException {
		final String commandName = "get-option";
		System.out.println("Logging script will ignore the " + commandName + " command.");
		return mScript.getOption(opt);
	}

	@Override
	public Object getInfo(final String info) throws UnsupportedOperationException {
		final StringWriter sw = new StringWriter();
		final PrintWriter mPw = new PrintWriter(sw);
		mPw.println("(get-info " + info + ")");
		final String commandName = "get-info";
		System.out.println("Logging script will ignore the " + commandName + " command.");
		return mScript.getInfo(info);
	}

	@Override
	public Term simplify(final Term term) throws SMTLIBException {
		final StringWriter sw = new StringWriter();
		final PrintWriter mPw = new PrintWriter(sw);
		mPw.print("(simplify ");
		mTermPrinter.append(mPw, term);
		mPw.println(")");
		final String commandName = "simplify";
		System.out.println("Logging script will ignore the " + commandName + " command.");
		return mScript.simplify(term);
	}

	@Override
	public void reset() {
		final StringWriter sw = new StringWriter();
		final PrintWriter mPw = new PrintWriter(sw);
		mPw.println("(reset)");
		resetAssertionStack();
		mScript.reset();
	}

	@Override
	public Term[] getInterpolants(final Term[] partition) throws SMTLIBException, UnsupportedOperationException {
		final StringWriter sw = new StringWriter();
		final PrintWriter mPw = new PrintWriter(sw);
		mPw.print("(get-interpolants");
		for (final Term t : partition) {
			mPw.print(' ');
			mTermPrinter.append(mPw, t);
		}
		mPw.println(')');
		final String commandName = "get-interpolants";
		System.out.println("Logging script will ignore the " + commandName + " command.");
		return mScript.getInterpolants(partition);
	}

	// [a,b,c], [0,1,0] -> a (b) c
	// c
	// a b
	@Override
	public Term[] getInterpolants(final Term[] partition, final int[] startOfSubtree)
			throws SMTLIBException, UnsupportedOperationException {
		final StringWriter sw = new StringWriter();
		final PrintWriter mPw = new PrintWriter(sw);
		mPw.print("(get-interpolants ");
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
		mPw.println(')');
		final String commandName = "get-interpolants";
		System.out.println("Logging script will ignore the " + commandName + " command.");
		return mScript.getInterpolants(partition, startOfSubtree);
	}

	@Override
	public void exit() {
		final StringWriter sw = new StringWriter();
		final PrintWriter mPw = new PrintWriter(sw);
		mPw.println("(exit)");
		mPw.flush();
		mPw.close();
		final String commandName = "exit";
		System.out.println("Logging script will ignore the " + commandName + " command.");
		mScript.exit();
	}

	@Override
	public Model getModel() throws SMTLIBException, UnsupportedOperationException {
		final StringWriter sw = new StringWriter();
		final PrintWriter mPw = new PrintWriter(sw);
		mPw.println("(get-model)");
		final String commandName = "get-model";
		System.out.println("Logging script will ignore the " + commandName + " command.");
		return mScript.getModel();
	}

	@Override
	public Iterable<Term[]> checkAllsat(final Term[] predicates) throws SMTLIBException, UnsupportedOperationException {
		final StringWriter sw = new StringWriter();
		final PrintWriter mPw = new PrintWriter(sw);
		final PrintTerm pt = new PrintTerm();
		mPw.print("(check-allsat (");
		String spacer = "";
		for (final Term p : predicates) {
			mPw.print(spacer);
			pt.append(mPw, p);
			spacer = " ";
		}
		mPw.println("))");
		final String commandName = "check-allsat";
		System.out.println("Logging script will ignore the " + commandName + " command.");
		return mScript.checkAllsat(predicates);
	}

	@Override
	public Term[] findImpliedEquality(final Term[] x, final Term[] y) {
		final StringWriter sw = new StringWriter();
		final PrintWriter mPw = new PrintWriter(sw);
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
		final String commandName = "find-implied-equality";
		System.out.println("Logging script will ignore the " + commandName + " command.");
		return mScript.findImpliedEquality(x, y);
	}

	@Override
	public QuotedObject echo(final QuotedObject msg) {
		final StringWriter sw = new StringWriter();
		final PrintWriter mPw = new PrintWriter(sw);
		mPw.print("(echo ");
		mPw.print(msg);
		mPw.println(')');
		addToCurrentAssertionStack(new EchoCommand(msg));
		return mScript.echo(msg);
	}

	/**
	 * Write a comment to the generated SMTLIB dump file. Note that this function is only available in the LoggingScript
	 * and not in the interface {@link Script} since it only makes sense for logging and not for solving.
	 *
	 * @param comment
	 *            The comment to write to the dump file.
	 */
	public void comment(final String comment) {
		final StringWriter sw = new StringWriter();
		final PrintWriter mPw = new PrintWriter(sw);
		mPw.print("; ");
		mPw.println(comment);
		final String commandName = "comment";
		System.out.println("Logging script will ignore the " + commandName + " command.");
	}

	@Override
	public LBool checkSatAssuming(final Term... assumptions) throws SMTLIBException {
		throw new UnsupportedOperationException("Introduced in SMTInterpol 2.1-324-ga0525a0, not yet supported");
	}

	@Override
	public Term[] getUnsatAssumptions() throws SMTLIBException, UnsupportedOperationException {
		throw new UnsupportedOperationException("Introduced in SMTInterpol 2.1-324-ga0525a0, not yet supported");
	}

	@Override
	public void resetAssertions() {
		throw new UnsupportedOperationException("Introduced in SMTInterpol 2.1-324-ga0525a0, not yet supported");
	}
}
