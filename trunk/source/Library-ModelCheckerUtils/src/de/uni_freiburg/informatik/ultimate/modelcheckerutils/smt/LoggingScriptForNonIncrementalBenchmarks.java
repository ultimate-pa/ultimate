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
package de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt;

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintWriter;
import java.io.StringWriter;
import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.LinkedList;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.Assignments;
import de.uni_freiburg.informatik.ultimate.logic.Identifier;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.Model;
import de.uni_freiburg.informatik.ultimate.logic.PrintTerm;
import de.uni_freiburg.informatik.ultimate.logic.QuotedObject;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

/**
 * This is a wrapper around a {@link Script} that is used by Matthias in order
 * to generate benchmarks for the SMT-COMP 2015.
 * This class contains a lot of code duplication from Jürgen's Logging script.
 * This class is a hack and should be used with extreme caution.
 * @author Matthias Heizmann
 */
public class LoggingScriptForNonIncrementalBenchmarks implements Script {

	/**
	 * The actual script.
	 */
	private final Script mScript;

	/**
	 * The auxiliary class to print terms and sorts.
	 */
	private final PrintTerm mTermPrinter = new PrintTerm();
	
	private final String m_BaseFilename;
	private final String m_Directory;
	
	protected final LinkedList<ArrayList<String>> m_CommandStack;
	

	public LoggingScriptForNonIncrementalBenchmarks(Script script, String baseFilename,
			String directory) {
		super();
		mScript = script;
		m_BaseFilename = baseFilename;
		m_Directory = directory;
		m_CommandStack = new LinkedList<>();
		m_CommandStack.push(new ArrayList<String>());
	}
	
	protected LinkedList<ArrayList<String>> deepCopyOfCommandStack() {
		LinkedList<ArrayList<String>> result = new LinkedList<ArrayList<String>>();
		for (ArrayList<String> al : m_CommandStack) {
			result.add(new ArrayList<String>());
			for (String command : al) {
				result.getLast().add(command);
			}
		}
		return result;
	}

	
	private void addToCurrentAssertionStack(String string) {
		m_CommandStack.getLast().add(string);
	}
	
	private void printCommandStack(PrintWriter pw, LinkedList<ArrayList<String>> commandStack) {
		for (ArrayList<String> al : commandStack) {
			for (String command : al) {
				pw.print(command);
			}
		}
	}
	
	protected void writeCommandStackToFile(File file, LinkedList<ArrayList<String>> commandStack) {
		FileWriter fw = null;
		try {
			fw = new FileWriter(file);
		} catch (IOException e) {
			throw new AssertionError("Unable to write file " + file);
		}
		PrintWriter pw = new PrintWriter(fw);
		printCommandStack(pw, commandStack);
		pw.close();
	}
	
	protected File constructFile(String suffix) {
		String filename = m_Directory + File.separator + m_BaseFilename + suffix + ".smt2";
		File file = new File(filename);
		return file;
	}

	private final Term formatTerm(Term input) {
//		return mLetter == null ? input : new FormulaLet().let(input);
		return input;
	}

	@Override
	public void setLogic(String logic)
		throws UnsupportedOperationException, SMTLIBException {
		StringWriter sw = new StringWriter();
		PrintWriter mPw = new PrintWriter(sw);
		mPw.println("(set-logic " + logic + ")");
		addToCurrentAssertionStack(sw.toString());
		mScript.setLogic(logic);
	}
	
	@Override
	public void setLogic(Logics logic)
		throws UnsupportedOperationException, SMTLIBException {
		StringWriter sw = new StringWriter();
		PrintWriter mPw = new PrintWriter(sw);
		mPw.println("(set-logic " + logic.name() + ")");
		addToCurrentAssertionStack(sw.toString());
		mScript.setLogic(logic);
	}



	@Override
	public void setOption(String opt, Object value)
		throws UnsupportedOperationException, SMTLIBException {
		StringWriter sw = new StringWriter();
		PrintWriter mPw = new PrintWriter(sw);
		mPw.print("(set-option ");
		mPw.print(opt);
		mPw.print(' ');
		new PrintTerm().append(mPw, value);
		mPw.println(")");
		addToCurrentAssertionStack(sw.toString());
		mScript.setOption(opt, value);
	}

	@Override
	public void setInfo(String info, Object value) {
		StringWriter sw = new StringWriter();
		PrintWriter mPw = new PrintWriter(sw);
		mPw.print("(set-info ");
		mPw.print(info);
		mPw.print(' ');
		new PrintTerm().append(mPw, value);
		mPw.println(")");
		addToCurrentAssertionStack(sw.toString());
		mScript.setInfo(info, value);
	}

	@Override
	public void declareSort(String sort, int arity) throws SMTLIBException {
		StringWriter sw = new StringWriter();
		PrintWriter mPw = new PrintWriter(sw);
		mPw.print("(declare-sort ");
		mPw.print(Identifier.quoteIdentifier(sort));
		mPw.print(' ');
		mPw.print(arity);
		mPw.println(")");
		addToCurrentAssertionStack(sw.toString());
		mScript.declareSort(sort, arity);
	}

	@Override
	public void defineSort(String sort, Sort[] sortParams, Sort definition)
		throws SMTLIBException {
		StringWriter sw = new StringWriter();
		PrintWriter mPw = new PrintWriter(sw);
		mPw.print("(define-sort ");
		mPw.print(Identifier.quoteIdentifier(sort));
		mPw.print(" (");
		String sep = "";
		for (Sort p : sortParams) {
			mPw.print(sep);
			mTermPrinter.append(mPw, p);
			sep = " ";
		}
		mPw.print(") ");
		mTermPrinter.append(mPw, definition);
		mPw.println(")");
		addToCurrentAssertionStack(sw.toString());
		mScript.defineSort(sort, sortParams, definition);
	}

	@Override
	public void declareFun(String fun, Sort[] paramSorts, Sort resultSort)
		throws SMTLIBException {
		StringWriter sw = new StringWriter();
		PrintWriter mPw = new PrintWriter(sw);
		mPw.print("(declare-fun ");
		mPw.print(Identifier.quoteIdentifier(fun));
		mPw.print(" (");
		String sep = "";
		for (Sort p : paramSorts) {
			mPw.print(sep);
			mTermPrinter.append(mPw, p);
			sep = " ";
		}
		mPw.print(") ");
		mTermPrinter.append(mPw, resultSort);
		mPw.println(")");
		addToCurrentAssertionStack(sw.toString());
		mScript.declareFun(fun, paramSorts, resultSort);
	}

	@Override
	public void defineFun(String fun, TermVariable[] params, Sort resultSort,
			Term definition) throws SMTLIBException {
		StringWriter sw = new StringWriter();
		PrintWriter mPw = new PrintWriter(sw);
		mPw.print("(define-fun ");
		mPw.print(Identifier.quoteIdentifier(fun));
		mPw.print(" (");
		String sep = "(";
		for (TermVariable t : params) {
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
		addToCurrentAssertionStack(sw.toString());
		mScript.defineFun(fun, params, resultSort, definition);
	}

	@Override
	public void push(int levels) throws SMTLIBException {
//		StringWriter sw = new StringWriter();
//		PrintWriter mPw = new PrintWriter(sw);
//		mPw.println("(push " + levels + ")");
//		addToCurrentAssertionStack(sw.toString());
		for (int i=0; i<levels; i++) {
			m_CommandStack.add(new ArrayList<String>());
		}
		mScript.push(levels);
	}

	@Override
	public void pop(int levels) throws SMTLIBException {
//		StringWriter sw = new StringWriter();
//		PrintWriter mPw = new PrintWriter(sw);
//		mPw.println("(pop " + levels + ")");
//		addToCurrentAssertionStack(sw.toString());
		for (int i=0; i<levels; i++) {
			m_CommandStack.removeLast();
		}
		mScript.pop(levels);
	}

	@Override
	public LBool assertTerm(Term term) throws SMTLIBException {
		StringWriter sw = new StringWriter();
		PrintWriter mPw = new PrintWriter(sw);
		mPw.print("(assert ");
		mTermPrinter.append(mPw, formatTerm(term));
		mPw.println(")");
		addToCurrentAssertionStack(sw.toString());
		return mScript.assertTerm(term);
	}

	@Override
	public LBool checkSat() throws SMTLIBException {
		StringWriter sw = new StringWriter();
		PrintWriter mPw = new PrintWriter(sw);
		mPw.println("(check-sat)");
		addToCurrentAssertionStack(sw.toString());
		return mScript.checkSat();
	}

	@Override
	public Term[] getAssertions() throws SMTLIBException {
		StringWriter sw = new StringWriter();
		PrintWriter mPw = new PrintWriter(sw);
		mPw.println("(get-assertions)");
		addToCurrentAssertionStack(sw.toString());
		return mScript.getAssertions();
	}

	@Override
	public Term getProof() throws SMTLIBException,
			UnsupportedOperationException {
		StringWriter sw = new StringWriter();
		PrintWriter mPw = new PrintWriter(sw);
		mPw.println("(get-proof)");
		addToCurrentAssertionStack(sw.toString());
		return mScript.getProof();
	}

	@Override
	public Term[] getUnsatCore() throws SMTLIBException,
			UnsupportedOperationException {
		StringWriter sw = new StringWriter();
		PrintWriter mPw = new PrintWriter(sw);
		mPw.println("(get-unsat-core)");
		addToCurrentAssertionStack(sw.toString());
		return mScript.getUnsatCore();
	}

	@Override
	public Map<Term, Term> getValue(Term[] terms) throws SMTLIBException,
			UnsupportedOperationException {
		StringWriter sw = new StringWriter();
		PrintWriter mPw = new PrintWriter(sw);
		mPw.print("(get-value (");
		String sep = "";
		for (Term t : terms) {
			mPw.print(sep);
			mTermPrinter.append(mPw, formatTerm(t));
			sep = " ";
		}
		mPw.println("))");
		addToCurrentAssertionStack(sw.toString());
		return mScript.getValue(terms);
	}

	@Override
	public Assignments getAssignment() throws SMTLIBException,
			UnsupportedOperationException {
		StringWriter sw = new StringWriter();
		PrintWriter mPw = new PrintWriter(sw);
		mPw.println("(get-assignment)");
		addToCurrentAssertionStack(sw.toString());
		return mScript.getAssignment();
	}

	@Override
	public Object getOption(String opt) throws UnsupportedOperationException {
//		StringWriter sw = new StringWriter();
//		PrintWriter mPw = new PrintWriter(sw);
//		mPw.println("(get-option " + opt + ")");
//		addToCurrentAssertionStack(sw.toString());
		return mScript.getOption(opt);
	}

	@Override
	public Object getInfo(String info) throws UnsupportedOperationException {
		StringWriter sw = new StringWriter();
		PrintWriter mPw = new PrintWriter(sw);
		mPw.println("(get-info " + info + ")");
		addToCurrentAssertionStack(sw.toString());
		return mScript.getInfo(info);
	}

	@Override
	public Term simplify(Term term) throws SMTLIBException {
		StringWriter sw = new StringWriter();
		PrintWriter mPw = new PrintWriter(sw);
		mPw.print("(simplify ");
		mTermPrinter.append(mPw, term);
		mPw.println(")");
		addToCurrentAssertionStack(sw.toString());
		return mScript.simplify(term);
	}

	@Override
	public void reset() {
		StringWriter sw = new StringWriter();
		PrintWriter mPw = new PrintWriter(sw);
		mPw.println("(reset)");
		addToCurrentAssertionStack(sw.toString());
		mScript.reset();
	}

	@Override
	public Term[] getInterpolants(Term[] partition) throws SMTLIBException,
			UnsupportedOperationException {
		StringWriter sw = new StringWriter();
		PrintWriter mPw = new PrintWriter(sw);
		mPw.print("(get-interpolants");
		for (Term t : partition) {
			mPw.print(' ');
			mTermPrinter.append(mPw, t);
		}
		mPw.println(')');
		addToCurrentAssertionStack(sw.toString());
		return mScript.getInterpolants(partition);
	}
	
	// [a,b,c], [0,1,0] -> a (b) c
	//  c
	// a b
	@Override
	public Term[] getInterpolants(Term[] partition, int[] startOfSubtree)
		throws SMTLIBException,	UnsupportedOperationException {
		StringWriter sw = new StringWriter();
		PrintWriter mPw = new PrintWriter(sw);
		mPw.print("(get-interpolants ");
		mTermPrinter.append(mPw, partition[0]);
		for (int i = 1; i < partition.length; ++i) {
			int prevStart = startOfSubtree[i - 1];
			while (startOfSubtree[i] < prevStart) {
				mPw.print(')');
				prevStart = startOfSubtree[prevStart - 1];
			}
			mPw.print(' ');
			if (startOfSubtree[i] == i)
				mPw.print('(');
			mTermPrinter.append(mPw, partition[i]);
		}
		mPw.println(')');
		addToCurrentAssertionStack(sw.toString());
		return mScript.getInterpolants(partition, startOfSubtree);
	}

	@Override
	public void exit() {
		StringWriter sw = new StringWriter();
		PrintWriter mPw = new PrintWriter(sw);
		mPw.println("(exit)");
		mPw.flush();
		mPw.close();
		addToCurrentAssertionStack(sw.toString());
		mScript.exit();
	}

	@Override
	public Sort sort(String sortname, Sort... params) throws SMTLIBException {
		return mScript.sort(sortname, params);
	}

	@Override
	public Sort sort(String sortname, BigInteger[] indices, Sort... params)
		throws SMTLIBException {
		return mScript.sort(sortname, indices, params);
	}

	@Override
	public Term term(String funcname, Term... params) throws SMTLIBException {
		return mScript.term(funcname, params);
	}

	@Override
	public Term term(String funcname, BigInteger[] indices, Sort returnSort,
			Term... params) throws SMTLIBException {
		return mScript.term(funcname, indices, returnSort, params);
	}

	@Override
	public TermVariable variable(String varname, Sort sort)
		throws SMTLIBException {
		return mScript.variable(varname, sort);
	}

	@Override
	public Term quantifier(int quantor, TermVariable[] vars, Term body,
			Term[]... patterns) throws SMTLIBException {
		return mScript.quantifier(quantor, vars, body, patterns);
	}

	@Override
	public Term let(TermVariable[] vars, Term[] values, Term body)
		throws SMTLIBException {
		return mScript.let(vars, values, body);
	}

	@Override
	public Term annotate(Term t, Annotation... annotations)
		throws SMTLIBException {
		return mScript.annotate(t, annotations);
	}

	@Override
	public Term numeral(String num) throws SMTLIBException {
		return mScript.numeral(num);
	}

	@Override
	public Term numeral(BigInteger num) throws SMTLIBException {
		return mScript.numeral(num);
	}

	@Override
	public Term decimal(String decimal) throws SMTLIBException {
		return mScript.decimal(decimal);
	}

	@Override
	public Term decimal(BigDecimal decimal) throws SMTLIBException {
		return mScript.decimal(decimal);
	}

	@Override
	public Term string(String str) throws SMTLIBException {
		return mScript.string(str);
	}

	@Override
	public Term hexadecimal(String hex) throws SMTLIBException {
		return mScript.hexadecimal(hex);
	}

	@Override
	public Term binary(String bin) throws SMTLIBException {
		return mScript.binary(bin);
	}

	@Override
	public Sort[] sortVariables(String... names) throws SMTLIBException {
		return mScript.sortVariables(names);
	}

	@Override
	public Model getModel() throws SMTLIBException,
			UnsupportedOperationException {
		StringWriter sw = new StringWriter();
		PrintWriter mPw = new PrintWriter(sw);
		mPw.println("(get-model)");
		addToCurrentAssertionStack(sw.toString());
		return mScript.getModel();
	}

	@Override
	public Iterable<Term[]> checkAllsat(Term[] predicates)
		throws SMTLIBException,	UnsupportedOperationException {
		StringWriter sw = new StringWriter();
		PrintWriter mPw = new PrintWriter(sw);
		PrintTerm pt = new PrintTerm();
		mPw.print("(check-allsat (");
		String spacer = "";
		for (Term p : predicates) {
			mPw.print(spacer);
			pt.append(mPw, p);
			spacer = " ";
		}
		mPw.println("))");
		addToCurrentAssertionStack(sw.toString());
		return mScript.checkAllsat(predicates);
	}

	@Override
	public Term[] findImpliedEquality(Term[] x, Term[] y) {
		StringWriter sw = new StringWriter();
		PrintWriter mPw = new PrintWriter(sw);
		PrintTerm pt = new PrintTerm();
		mPw.print("(find-implied-equality (");
		String spacer = "";
		for (Term p : x) {
			mPw.print(spacer);
			pt.append(mPw, p);
			spacer = " ";
		}
		mPw.print(") (");
		spacer = "";
		for (Term p : x) {
			mPw.print(spacer);
			pt.append(mPw, p);
			spacer = " ";
		}
		mPw.println("))");
		addToCurrentAssertionStack(sw.toString());
		return mScript.findImpliedEquality(x, y);
	}
	
	@Override
	public QuotedObject echo(QuotedObject msg) {
//		StringWriter sw = new StringWriter();
//		PrintWriter mPw = new PrintWriter(sw);
//		mPw.print("(echo ");
//		mPw.print(msg);
//		mPw.println(')');
//		addToCurrentAssertionStack(sw.toString());
		return mScript.echo(msg);
	}
	
	/**
	 * Write a comment to the generated SMTLIB dump file.  Note that this
	 * function is only available in the LoggingScript and not in the interface
	 * {@link Script} since it only makes sense for logging and not for solving.
	 * @param comment The comment to write to the dump file.
	 */
	public void comment(String comment) {
		StringWriter sw = new StringWriter();
		PrintWriter mPw = new PrintWriter(sw);
		mPw.print("; ");
		mPw.println(comment);
		addToCurrentAssertionStack(sw.toString());
	}
}
