/*
 * Copyright (C) 2013-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 Oday Jubran
 * Copyright (C) 2015 University of Freiburg
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

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.OutputStreamWriter;
import java.io.PrintWriter;
import java.util.ArrayList;
import java.util.LinkedList;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Assignments;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.Model;
import de.uni_freiburg.informatik.ultimate.logic.NoopScript;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.smtsolver.external.SmtCommandUtils.AssertCommand;
import de.uni_freiburg.informatik.ultimate.smtsolver.external.SmtCommandUtils.DeclareFunCommand;
import de.uni_freiburg.informatik.ultimate.smtsolver.external.SmtCommandUtils.DeclareSortCommand;
import de.uni_freiburg.informatik.ultimate.smtsolver.external.SmtCommandUtils.DefineFunCommand;
import de.uni_freiburg.informatik.ultimate.smtsolver.external.SmtCommandUtils.DefineSortCommand;
import de.uni_freiburg.informatik.ultimate.smtsolver.external.SmtCommandUtils.ISmtCommand;
import de.uni_freiburg.informatik.ultimate.smtsolver.external.SmtCommandUtils.ResetCommand;
import de.uni_freiburg.informatik.ultimate.smtsolver.external.SmtCommandUtils.SetInfoCommand;
import de.uni_freiburg.informatik.ultimate.smtsolver.external.SmtCommandUtils.SetLogicCommand;
import de.uni_freiburg.informatik.ultimate.smtsolver.external.SmtCommandUtils.SetOptionCommand;

/**
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 */
public class NonIncrementalScriptor extends NoopScript {

	private static final String PRINT_SUCCESS = ":print-success";
	protected final LinkedList<ArrayList<ISmtCommand<?>>> mCommandStack;
	
	protected Executor mExecutor;
	private final LBool mStatus = LBool.UNKNOWN;
	
	/**
	 * For wrinting logs 
	 */
	private final PrintWriter mPw;

	/**
	 * Create a script connecting to an external SMT solver.
	 * 
	 * @param command
	 *            the command that starts the external SMT solver. The solver is expected to read smtlib 2 commands on
	 *            stdin.
	 * @param services
	 * @param storage
	 * @param dumpFakeNonIncrementalScript 
	 * @param basenameOfDumpedFakeNonIcrementalScript 
	 * @param pathOfDumpedFakeNonIncrementalScript 
	 * @throws IOExceptionO
	 *             If the solver is not installed
	 */
	public NonIncrementalScriptor(final String command, final ILogger logger, 
			final IUltimateServiceProvider services, final IToolchainStorage storage,
			final String solverName, final boolean dumpFakeNonIncrementalScript, 
			final String pathOfDumpedFakeNonIncrementalScript, final String basenameOfDumpedFakeNonIcrementalScript) throws IOException {
		if (dumpFakeNonIncrementalScript) {
			final String fullFilename = pathOfDumpedFakeNonIncrementalScript + 
					File.separator + basenameOfDumpedFakeNonIcrementalScript +
					"_fakeNonIncremental.smt2";
			mPw = new PrintWriter(
					new BufferedWriter(new OutputStreamWriter(new FileOutputStream(fullFilename))), true);
		} else {
			mPw = null;
		}
		mExecutor = new Executor(command, this, logger, services, storage, solverName);
		mCommandStack = new LinkedList<>();
		mCommandStack.push(new ArrayList<ISmtCommand<?>>());
	}
	
	protected void addToCurrentAssertionStack(final ISmtCommand<?> smtCommand) {
		mCommandStack.getLast().add(smtCommand);
	}
	
	private void resetAssertionStack() {
		mCommandStack.clear();
		mCommandStack.add(new ArrayList<>());
	}

	@Override
	public void setLogic(final Logics logic) throws UnsupportedOperationException, SMTLIBException {
		super.setLogic(logic);
		addToCurrentAssertionStack(new SetLogicCommand(logic.name()));
	}

	@Override
	public void setOption(final String opt, final Object value) throws UnsupportedOperationException, SMTLIBException {
		if (!opt.equals(PRINT_SUCCESS)) {
			addToCurrentAssertionStack(new SetOptionCommand(opt, value));
		}
	}

	@Override
	public void setInfo(final String info, final Object value) {
		addToCurrentAssertionStack(new SetInfoCommand(info, value));
	}

	@Override
	public void declareSort(final String sort, final int arity) throws SMTLIBException {
		super.declareSort(sort, arity);
		addToCurrentAssertionStack(new DeclareSortCommand(sort, arity));
	}

	@Override
	public void defineSort(final String sort, final Sort[] sortParams, final Sort definition) throws SMTLIBException {
		super.defineSort(sort, sortParams, definition);
		addToCurrentAssertionStack(new DefineSortCommand(sort, sortParams, definition));
	}

	@Override
	public void declareFun(final String fun, final Sort[] paramSorts, final Sort resultSort) throws SMTLIBException {
		super.declareFun(fun, paramSorts, resultSort);
		addToCurrentAssertionStack(new DeclareFunCommand(fun, paramSorts, resultSort));
	}

	@Override
	public void defineFun(final String fun, final TermVariable[] params, final Sort resultSort, final Term definition) throws SMTLIBException {
		super.defineFun(fun, params, resultSort, definition);
		addToCurrentAssertionStack(new DefineFunCommand(fun, params, resultSort, definition));
	}

	@Override
	public void push(final int levels) throws SMTLIBException {
		super.push(levels);
		for (int i = 0; i < levels; i++) {
			mCommandStack.add(new ArrayList<ISmtCommand<?>>());
		}
	}

	@Override
	public void pop(final int levels) throws SMTLIBException {
		super.pop(levels);
		for (int i = 0; i < levels; i++) {
			mCommandStack.removeLast();
		}
	}

	@Override
	public LBool assertTerm(final Term term) throws SMTLIBException {
		addToCurrentAssertionStack(new AssertCommand(term)); 
		return LBool.UNKNOWN;
	}

	@Override
	public LBool checkSat() throws SMTLIBException {
		(new ResetCommand()).executeWithExecutor(mExecutor, mPw);
		(new SetOptionCommand(PRINT_SUCCESS, true)).executeWithExecutor(mExecutor, mPw);
		for (final ArrayList<ISmtCommand<?>> level : mCommandStack) {
			for (final ISmtCommand<?> command : level) {
				command.executeWithExecutor(mExecutor, mPw);
			}
		}
		return (new SmtCommandUtils.CheckSatCommand()).executeWithExecutor(mExecutor, mPw);
	}

	@Override
	public Term[] getAssertions() throws SMTLIBException {
		mExecutor.input("(get-assertions)");
		return mExecutor.parseGetAssertionsResult();
	}

	/** Proofs are not supported, since they are not standardized **/
	@Override
	public Term getProof() throws SMTLIBException, UnsupportedOperationException {
		throw new UnsupportedOperationException("Proofs are not supported");
	}

	@Override
	public Term[] getUnsatCore() throws SMTLIBException, UnsupportedOperationException {
		mExecutor.input(SmtCommandUtils.GetUnsatCoreCommand.buildString());
		return mExecutor.parseGetUnsatCoreResult();
	}

	@Override
	public Map<Term, Term> getValue(final Term[] terms) throws SMTLIBException, UnsupportedOperationException {
		for (final Term t : terms) {
			if (!t.getSort().isNumericSort() && t.getSort() != getTheory().getBooleanSort()
					&& !t.getSort().getRealSort().getName().equals("BitVec")
					&& !t.getSort().getRealSort().getName().equals("FloatingPoint")) {
				throw new UnsupportedOperationException();
			}
		}
		mExecutor.input(SmtCommandUtils.GetValueCommand.buildString(terms));
		return mExecutor.parseGetValueResult();
	}

	@Override
	public Assignments getAssignment() throws SMTLIBException, UnsupportedOperationException {
		mExecutor.input("(get-assignment)");
		return mExecutor.parseGetAssignmentResult();
	}

	@Override
	public Object getOption(final String opt) throws UnsupportedOperationException {
		mExecutor.input("(get-option " + opt + ")");
		return mExecutor.parseGetOptionResult();
	}

	@Override
	public Object getInfo(final String info) throws UnsupportedOperationException {
		mExecutor.input("(get-info " + info + ")");
		final Object[] result = mExecutor.parseGetInfoResult();
		if (result.length == 1) {
			return result[0];
		}
		return result;
	}

	@Override
	public void exit() {
		mExecutor.exit();

	}

	@Override
	public Term simplify(final Term term) throws SMTLIBException {
		throw new UnsupportedOperationException();
	}

	@Override
	public void reset() {
		super.reset();
		try {
			mExecutor.reset();
		} catch (final IOException e) {
			// this should only happen if the solver executable is removed
			// between creating executor and calling reset.
			e.printStackTrace();
		}
	}

	@Override
	public Model getModel() throws SMTLIBException, UnsupportedOperationException {
		throw new UnsupportedOperationException();
	}

	/** This method is used in the output parser, to support (get-info :status) **/
	public LBool getStatus() {
		return mStatus;
	}
	
	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();
		boolean isFirst = true;
		for (final ArrayList<ISmtCommand<?>> level : mCommandStack) {
			if (isFirst) {
				isFirst = false;
			} else {
				sb.append("; next level of assertion stack").append(System.lineSeparator());
			}
			for (final ISmtCommand<?> command : level) {
				sb.append(command.toString()).append(System.lineSeparator());
			}
		}
		return sb.toString();
	}

}
