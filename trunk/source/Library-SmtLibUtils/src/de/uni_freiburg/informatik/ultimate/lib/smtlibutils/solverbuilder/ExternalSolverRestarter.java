/*
 * Copyright (C) 2026 University of Freiburg
 * Copyright (C) 2026 LMU Munich
 * Copyright (C) 2026 Max Barth (Max.Barth@lmu.de)
 *
 * This file is part of the ULTIMATE SmtLibUtils Library.
 *
 * The ULTIMATE SmtLibUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE SmtLibUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE SmtLibUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE SmtLibUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE SmtLibUtils Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.smtlibutils.solverbuilder;

import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.scripttransfer.HistoryRecordingScript;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.NoopScript;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.smtsolver.external.Scriptor;
import de.uni_freiburg.informatik.ultimate.smtsolver.external.SmtCommandUtils;

/**
 * Restarts an external solver that died, e.g. of an interrupt from {@link ExternalSolverInterrupter} that arrived just
 * after the solver had answered, and brings the new process back to the declarations and the stack of the script.
 * <p>
 * The declarations come from the {@link HistoryRecordingScript} that {@link SolverBuilder} wraps around every script.
 * Assertions are not restored: the caller has to be in a scope whose assertions it rebuilds anyway, like k-induction,
 * which asserts only inside the push of a query and repeats an interrupted query from scratch.
 *
 * @author Max Barth (Max.Barth@lmu.de)
 */
public final class ExternalSolverRestarter {

	private ExternalSolverRestarter() {
		// static methods only
	}

	/**
	 * Restarts the solver behind {@code script} and replays its declarations and pushes.
	 *
	 * @throws UnsupportedOperationException
	 *             if {@code script} has no {@link HistoryRecordingScript} or is not backed by an external solver
	 */
	public static void restartAndReplay(final Script script) {
		final HistoryRecordingScript history = HistoryRecordingScript.extractHistoryRecordingScript(script);
		if (history == null) {
			throw new UnsupportedOperationException(
					"cannot restart the solver: " + script + " has no " + HistoryRecordingScript.class.getSimpleName()
							+ ", so its declarations are unknown");
		}
		final Scriptor scriptor = ExternalSolverInterrupter.findScriptor(script);
		final CommandRecorder recorder = new CommandRecorder();
		history.transferHistoryFromRecord(recorder);
		scriptor.restartAndReplay(recorder.getCommands());
	}

	/**
	 * Turns the replayed history into the commands {@link Scriptor} would have sent. It keeps a theory of its own, so
	 * that sorts and definitions can refer to what was declared before, without clashing with the original script.
	 */
	private static final class CommandRecorder extends NoopScript {
		private final List<String> mCommands = new ArrayList<>();

		CommandRecorder() {
			setLogic(Logics.ALL);
		}

		List<String> getCommands() {
			return mCommands;
		}

		@Override
		public void declareSort(final String sort, final int arity) throws SMTLIBException {
			super.declareSort(sort, arity);
			mCommands.add(SmtCommandUtils.DeclareSortCommand.buildString(sort, arity));
		}

		@Override
		public void defineSort(final String sort, final Sort[] sortParams, final Sort definition)
				throws SMTLIBException {
			super.defineSort(sort, sortParams, definition);
			mCommands.add(SmtCommandUtils.DefineSortCommand.buildString(sort, sortParams, definition));
		}

		@Override
		public void declareFun(final String fun, final Sort[] paramSorts, final Sort resultSort)
				throws SMTLIBException {
			super.declareFun(fun, paramSorts, resultSort);
			mCommands.add(SmtCommandUtils.DeclareFunCommand.buildString(fun, paramSorts, resultSort));
		}

		@Override
		public void defineFun(final String fun, final TermVariable[] params, final Sort resultSort,
				final Term definition) throws SMTLIBException {
			super.defineFun(fun, params, resultSort, definition);
			mCommands.add(SmtCommandUtils.DefineFunCommand.buildString(fun, params, resultSort, definition));
		}

		@Override
		public void push(final int levels) throws SMTLIBException {
			super.push(levels);
			mCommands.add("(push " + levels + ")");
		}
	}
}
