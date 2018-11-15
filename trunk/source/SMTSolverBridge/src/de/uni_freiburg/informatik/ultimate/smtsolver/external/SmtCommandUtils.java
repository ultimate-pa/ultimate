/*
 * Copyright (C) 2016 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
 *
 * This file is part of the ULTIMATE SMTSolverBridge.
 *
 * The ULTIMATE SMTSolverBridge is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE SMTSolverBridge is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE SMTSolverBridge. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE SMTSolverBridge, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE SMTSolverBridge grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.smtsolver.external;

import java.io.PrintWriter;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.logic.PrintTerm;
import de.uni_freiburg.informatik.ultimate.logic.QuotedObject;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

public class SmtCommandUtils {

	public interface ISmtCommand<RT> {

		public abstract RT executeWithScript(Script script);

		public abstract RT executeWithExecutor(Executor executor, PrintWriter pw);

		/**
		 *
		 * @return the representation of the command that can be passed to an SMT solver
		 */
		@Override
		public abstract String toString();
	}

	public static class SetLogicCommand implements ISmtCommand<Void> {
		private final String mLogic;

		public SetLogicCommand(final String logic) {
			mLogic = logic;
		}

		public static String buildString(final String logic) {
			return "(set-logic " + logic + ")";
		}

		@Override
		public Void executeWithScript(final Script script) {
			script.setLogic(mLogic);
			return null;
		}

		@Override
		public String toString() {
			return buildString(mLogic);
		}

		@Override
		public Void executeWithExecutor(final Executor executor, final PrintWriter pw) {
			final String command = toString();
			if (pw != null) {
				pw.println(command);
			}
			executor.input(command);
			executor.parseSuccess();
			return null;
		}
	}

	public static class SetOptionCommand implements ISmtCommand<Void> {
		private final String mOpt;
		private final Object mValue;

		public SetOptionCommand(final String opt, final Object value) {
			super();
			mOpt = opt;
			mValue = value;
		}

		public static String buildString(final String opt, final Object value) {
			final StringBuilder sb = new StringBuilder();
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
			return sb.toString();
		}

		@Override
		public Void executeWithScript(final Script script) {
			script.setOption(mOpt, mValue);
			return null;
		}

		@Override
		public String toString() {
			return buildString(mOpt, mValue);
		}

		@Override
		public Void executeWithExecutor(final Executor executor, final PrintWriter pw) {
			final String command = toString();
			if (pw != null) {
				pw.println(command);
			}
			executor.input(command);
			executor.parseSuccess();
			return null;
		}
	}

	public static class SetInfoCommand implements ISmtCommand<Void> {
		private final String mInfo;
		private final Object mValue;

		public SetInfoCommand(final String info, final Object value) {
			super();
			mInfo = info;
			mValue = value;
		}

		public static String buildString(final String info, final Object value) {
			final StringBuilder sb = new StringBuilder();
			sb.append("(set-info ");
			sb.append(info);
			sb.append(' ');
			sb.append(PrintTerm.quoteObjectIfString(value));
			sb.append(")");
			sb.append(System.lineSeparator());
			return sb.toString();
		}

		@Override
		public Void executeWithScript(final Script script) {
			script.setInfo(mInfo, mValue);
			return null;
		}

		@Override
		public String toString() {
			return buildString(mInfo, mValue);
		}

		@Override
		public Void executeWithExecutor(final Executor executor, final PrintWriter pw) {
			final String command = toString();
			if (pw != null) {
				pw.println(command);
			}
			executor.input(command);
			executor.parseSuccess();
			return null;
		}
	}

	public static class DeclareSortCommand implements ISmtCommand<Void> {
		private final String mSort;
		private final int mArity;

		public DeclareSortCommand(final String sort, final int arity) {
			super();
			mSort = sort;
			mArity = arity;
		}

		public static String buildString(final String sort, final int arity) {
			final StringBuilder sb = new StringBuilder("(declare-sort ").append(PrintTerm.quoteIdentifier(sort));
			sb.append(" ").append(arity).append(")");
			return sb.toString();
		}

		@Override
		public Void executeWithScript(final Script script) {
			script.declareSort(mSort, mArity);
			return null;
		}

		@Override
		public String toString() {
			return buildString(mSort, mArity);
		}

		@Override
		public Void executeWithExecutor(final Executor executor, final PrintWriter pw) {
			final String command = toString();
			if (pw != null) {
				pw.println(command);
			}
			executor.input(command);
			executor.parseSuccess();
			return null;
		}
	}

	public static class DefineSortCommand implements ISmtCommand<Void> {
		private final String mSort;
		private final Sort[] mSortParams;
		private final Sort mDefinition;

		public DefineSortCommand(final String sort, final Sort[] sortParams, final Sort definition) {
			super();
			mSort = sort;
			mSortParams = sortParams;
			mDefinition = definition;
		}

		public static String buildString(final String sort, final Sort[] sortParams, final Sort definition) {
			final PrintTerm pt = new PrintTerm();
			final StringBuilder sb = new StringBuilder();
			sb.append("(define-sort ");
			sb.append(PrintTerm.quoteIdentifier(sort));
			sb.append(" (");
			String delim = "";
			for (final Sort s : sortParams) {
				sb.append(delim);
				pt.append(sb, s);
				delim = " ";
			}
			sb.append(") ");
			pt.append(sb, definition);
			sb.append(")");
			return sb.toString();
		}

		@Override
		public Void executeWithScript(final Script script) {
			script.defineSort(mSort, mSortParams, mDefinition);
			return null;
		}

		@Override
		public String toString() {
			return buildString(mSort, mSortParams, mDefinition);
		}

		@Override
		public Void executeWithExecutor(final Executor executor, final PrintWriter pw) {
			final String command = toString();
			if (pw != null) {
				pw.println(command);
			}
			executor.input(command);
			executor.parseSuccess();
			return null;
		}

	}

	public static class DeclareFunCommand implements ISmtCommand<Void> {
		final String mFun;
		final Sort[] mParamSorts;
		final Sort mResultSort;

		public DeclareFunCommand(final String fun, final Sort[] paramSorts, final Sort resultSort) {
			super();
			mFun = fun;
			mParamSorts = paramSorts;
			mResultSort = resultSort;
		}

		public static String buildString(final String fun, final Sort[] paramSorts, final Sort resultSort) {
			final PrintTerm pt = new PrintTerm();
			final StringBuilder sb = new StringBuilder();
			sb.append("(declare-fun ");
			sb.append(PrintTerm.quoteIdentifier(fun));
			sb.append(" (");
			String delim = "";
			for (final Sort s : paramSorts) {
				sb.append(delim);
				pt.append(sb, s);
				delim = " ";
			}
			sb.append(") ");
			pt.append(sb, resultSort);
			sb.append(")");
			return sb.toString();
		}

		@Override
		public Void executeWithScript(final Script script) {
			script.declareFun(mFun, mParamSorts, mResultSort);
			return null;
		}

		@Override
		public String toString() {
			return buildString(mFun, mParamSorts, mResultSort);
		}

		@Override
		public Void executeWithExecutor(final Executor executor, final PrintWriter pw) {
			final String command = toString();
			if (pw != null) {
				pw.println(command);
			}
			executor.input(command);
			executor.parseSuccess();
			return null;
		}

	}

	public static class DefineFunCommand implements ISmtCommand<Void> {
		final String mFun;
		final TermVariable[] mParams;
		final Sort mResultSort;
		final Term mDefinition;

		public DefineFunCommand(final String fun, final TermVariable[] params, final Sort resultSort,
				final Term definition) {
			super();
			mFun = fun;
			mParams = params;
			mResultSort = resultSort;
			mDefinition = definition;
		}

		public static String buildString(final String fun, final TermVariable[] params, final Sort resultSort,
				final Term definition) {
			final PrintTerm pt = new PrintTerm();
			final StringBuilder sb = new StringBuilder();
			sb.append("(define-fun ");
			sb.append(PrintTerm.quoteIdentifier(fun));
			sb.append(" (");
			String delim = "";
			for (final TermVariable t : params) {
				sb.append(delim);
				sb.append("(").append(t).append(" ");
				pt.append(sb, t.getSort());
				sb.append(")");
				delim = " ";
			}
			sb.append(") ");
			pt.append(sb, resultSort);
			sb.append(" ");
			pt.append(sb, definition);
			sb.append(")");
			return sb.toString();
		}

		@Override
		public Void executeWithScript(final Script script) {
			script.defineFun(mFun, mParams, mResultSort, mDefinition);
			return null;
		}

		@Override
		public String toString() {
			return buildString(mFun, mParams, mResultSort, mDefinition);
		}

		@Override
		public Void executeWithExecutor(final Executor executor, final PrintWriter pw) {
			final String command = toString();
			if (pw != null) {
				pw.println(command);
			}
			executor.input(command);
			executor.parseSuccess();
			return null;
		}

	}

	public static class AssertCommand implements ISmtCommand<Void> {
		private final Term mTerm;

		public AssertCommand(final Term term) {
			super();
			mTerm = term;
		}

		public static String buildString(final Term term) {
			return "(assert " + term.toString() + ")";
		}

		@Override
		public Void executeWithScript(final Script script) {
			script.assertTerm(mTerm);
			return null;
		}

		@Override
		public String toString() {
			return buildString(mTerm);
		}

		@Override
		public Void executeWithExecutor(final Executor executor, final PrintWriter pw) {
			final String command = toString();
			if (pw != null) {
				pw.println(command);
			}
			executor.input(command);
			executor.parseSuccess();
			return null;
		}
	}

	public static class ResetCommand implements ISmtCommand<Void> {
		public static String buildString() {
			return "(reset)";
		}

		@Override
		public Void executeWithScript(final Script script) {
			script.reset();
			return null;
		}

		@Override
		public String toString() {
			return buildString();
		}

		@Override
		public Void executeWithExecutor(final Executor executor, final PrintWriter pw) {
			final String command = toString();
			if (pw != null) {
				pw.println(command);
			}
			executor.input(command);
			executor.parseSuccess();
			return null;
		}
	}

	public static class CheckSatCommand implements ISmtCommand<LBool> {
		public static String buildString() {
			return "(check-sat)";
		}

		@Override
		public LBool executeWithScript(final Script script) {
			return script.checkSat();
		}

		@Override
		public String toString() {
			return buildString();
		}

		@Override
		public LBool executeWithExecutor(final Executor executor, final PrintWriter pw) {
			final String command = toString();
			if (pw != null) {
				pw.println(command);
			}
			executor.input(command);
			return executor.parseCheckSatResult();
		}
	}

	public static class EchoCommand implements ISmtCommand<Void> {
		final QuotedObject mMsg;

		public EchoCommand(final QuotedObject msg) {
			super();
			mMsg = msg;
		}

		@Override
		public Void executeWithScript(final Script script) {
			script.echo(mMsg);
			return null;
		}

		public static String buildString(final QuotedObject msg) {
			return "(echo " + msg + ")";
		}

		@Override
		public String toString() {
			return buildString(mMsg);
		}

		@Override
		public Void executeWithExecutor(final Executor executor, final PrintWriter pw) {
			final String command = toString();
			if (pw != null) {
				pw.println(command);
			}
			executor.input(command);
			executor.parseSuccess();
			return null;
		}
	}

	public static class GetUnsatCoreCommand implements ISmtCommand<Term[]> {
		public static String buildString() {
			return "(get-unsat-core)";
		}

		@Override
		public Term[] executeWithScript(final Script script) {
			return script.getUnsatCore();
		}

		@Override
		public String toString() {
			return buildString();
		}

		@Override
		public Term[] executeWithExecutor(final Executor executor, final PrintWriter pw) {
			final String command = toString();
			if (pw != null) {
				pw.println(command);
			}
			executor.input(command);
			return executor.parseGetUnsatCoreResult();
		}
	}

	public static class GetValueCommand implements ISmtCommand<Map<Term, Term>> {
		final Term[] mTerms;

		public GetValueCommand(final Term[] terms) {
			super();
			mTerms = terms;
		}

		public static String buildString(final Term[] terms) {
			final StringBuilder command = new StringBuilder();
			final PrintTerm pt = new PrintTerm();
			command.append("(get-value (");
			String sep = "";
			for (final Term t : terms) {
				command.append(sep);
				pt.append(command, t);
				sep = " ";
			}
			command.append("))");
			return command.toString();
		}

		@Override
		public Map<Term, Term> executeWithScript(final Script script) {
			return script.getValue(mTerms);
		}

		@Override
		public String toString() {
			return buildString(mTerms);
		}

		@Override
		public Map<Term, Term> executeWithExecutor(final Executor executor, final PrintWriter pw) {
			return executor.parseGetValueResult();
		}
	}

}
