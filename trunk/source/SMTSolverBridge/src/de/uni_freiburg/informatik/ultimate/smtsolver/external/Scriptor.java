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

import java.io.IOException;
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

/**
 * Create a script that connects to an external SMT solver. The solver must be SMTLIB-2 compliant and expect commands on
 * standard input. It must return its output on standard output.
 * 
 * Some commands are only partially supported. For example getProof does not return a useful proof object. Also
 * commands, for which the output format is not fully specified, e.g. (get-model), may not return useful return values.
 * 
 * @author Oday Jubran
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 */
public class Scriptor extends NoopScript {

	protected Executor mExecutor;
	private LBool mStatus = LBool.UNKNOWN;

	/**
	 * Create a script connecting to an external SMT solver.
	 * 
	 * @param command
	 *            the command that starts the external SMT solver. The solver is expected to read smtlib 2 commands on
	 *            stdin.
	 * @param services
	 * @param storage
	 * @throws IOExceptionO
	 *             If the solver is not installed
	 */
	public Scriptor(final String command, final ILogger logger, final IUltimateServiceProvider services,
			final IToolchainStorage storage, final String solverName) throws IOException {
		mExecutor = new Executor(command, this, logger, services, storage, solverName);
		super.setOption(":print-success", true);
	}

	@Override
	public void setLogic(final Logics logic) throws UnsupportedOperationException, SMTLIBException {
		super.setLogic(logic);
		mExecutor.input(SmtCommandUtils.SetLogicCommand.buildString(logic.name()));
		mExecutor.parseSuccess();
	}

	@Override
	public void setOption(final String opt, final Object value) throws UnsupportedOperationException, SMTLIBException {
		if (!opt.equals(":print-success")) {
			mExecutor.input(SmtCommandUtils.SetOptionCommand.buildString(opt, value));
			mExecutor.parseSuccess();
		}
	}

	@Override
	public void setInfo(final String info, final Object value) {
		mExecutor.input(SmtCommandUtils.SetInfoCommand.buildString(info, value));
		mExecutor.parseSuccess();
	}

	@Override
	public void declareSort(final String sort, final int arity) throws SMTLIBException {
		super.declareSort(sort, arity);
		mExecutor.input(SmtCommandUtils.DeclareSortCommand.buildString(sort, arity));
		mExecutor.parseSuccess();
	}

	@Override
	public void defineSort(final String sort, final Sort[] sortParams, final Sort definition) throws SMTLIBException {
		super.defineSort(sort, sortParams, definition);
		mExecutor.input(SmtCommandUtils.DefineSortCommand.buildString(sort, sortParams, definition));
		mExecutor.parseSuccess();
	}

	@Override
	public void declareFun(final String fun, final Sort[] paramSorts, final Sort resultSort) throws SMTLIBException {
		super.declareFun(fun, paramSorts, resultSort);

		mExecutor.input(SmtCommandUtils.DeclareFunCommand.buildString(fun, paramSorts, resultSort));
		mExecutor.parseSuccess();
	}

	@Override
	public void defineFun(final String fun, final TermVariable[] params, final Sort resultSort, final Term definition)
			throws SMTLIBException {
		super.defineFun(fun, params, resultSort, definition);
		mExecutor.input(SmtCommandUtils.DefineFunCommand.buildString(fun, params, resultSort, definition));
		mExecutor.parseSuccess();
	}

	@Override
	public void push(final int levels) throws SMTLIBException {
		super.push(levels);
		mExecutor.input("(push " + levels + ")");
		mExecutor.parseSuccess();
	}

	@Override
	public void pop(final int levels) throws SMTLIBException {
		super.pop(levels);
		mExecutor.input("(pop " + levels + ")");
		mExecutor.parseSuccess();
		mStatus = LBool.UNKNOWN;
	}

	@Override
	public LBool assertTerm(final Term term) throws SMTLIBException {
		mExecutor.input(SmtCommandUtils.AssertCommand.buildString(term));
		mExecutor.parseSuccess();
		mStatus = LBool.UNKNOWN;
		return LBool.UNKNOWN;
	}

	@Override
	public LBool checkSat() throws SMTLIBException {
		mExecutor.input(SmtCommandUtils.CheckSatCommand.buildString());
		mStatus = mExecutor.parseCheckSatResult();
		return mStatus;
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
				throw new UnsupportedOperationException("Cannot provide value for term " + t.toStringDirect()
						+ " of sort " + t.getSort().getRealSort());
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
		mStatus = LBool.UNKNOWN;
	}

	@Override
	public Model getModel() throws SMTLIBException, UnsupportedOperationException {
		throw new UnsupportedOperationException();
	}

	/** This method is used in the output parser, to support (get-info :status) **/
	public LBool getStatus() {
		return mStatus;
	}

}
