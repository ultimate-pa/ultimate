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

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.scripttransfer.HistoryRecordingScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.arrays.DiffWrapperScript;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.smtsolver.external.Scriptor;

/**
 * Interrupts the running check-sat of an external solver from another thread; see {@link Scriptor#interrupt()}. The
 * solver answers {@code unknown} and keeps its state (z3 does). If the signal arrives just after the solver answered,
 * the solver dies; {@link ExternalSolverRestarter} brings it back.
 *
 * @author Max Barth (Max.Barth@lmu.de)
 */
public final class ExternalSolverInterrupter {

	private ExternalSolverInterrupter() {
		// static methods only
	}

	/**
	 * @return the external solver behind {@code script}
	 * @throws UnsupportedOperationException
	 *             if {@code script} is not backed by an external solver, e.g. SMTInterpol
	 */
	public static Scriptor findScriptor(final Script script) {
		// WrapperScript.findBacking never reaches the innermost script, which is where the Scriptor is. Only the
		// wrappers that SolverBuilder puts around an external solver are looked through.
		Script current = script;
		while (true) {
			if (current instanceof final HistoryRecordingScript history) {
				current = history.getWrappedScript();
			} else if (current instanceof final DiffWrapperScript diff) {
				current = diff.getWrappedScript();
			} else {
				break;
			}
		}
		if (current instanceof final Scriptor scriptor) {
			return scriptor;
		}
		throw new UnsupportedOperationException("only an external solver (Scriptor) can be interrupted, but "
				+ (current == script ? "the script" : "the script behind " + script.getClass().getSimpleName())
				+ " is a " + current.getClass().getSimpleName());
	}

	/**
	 * @param graceMillis
	 *            how long to wait for the check-sat to end before killing the solver, or negative to never kill it; a
	 *            killed solver has to be restarted, see {@link ExternalSolverRestarter}
	 * @return whether a check-sat was running and got the signal
	 */
	public static boolean interrupt(final Script script, final long graceMillis) {
		return findScriptor(script).interrupt(graceMillis);
	}

	/**
	 * @return whether the last check-sat of {@code script} was interrupted
	 */
	public static boolean wasInterrupted(final Script script) {
		return findScriptor(script).wasInterrupted();
	}

	/**
	 * @return whether the solver of {@code script} was killed during its last check-sat, by an interrupt it did not
	 *         notice in time; it may have answered before
	 */
	public static boolean wasKilled(final Script script) {
		return findScriptor(script).wasKilled();
	}

	/**
	 * @return whether the solver process of {@code script} still runs
	 */
	public static boolean isAlive(final Script script) {
		return findScriptor(script).isSolverAlive();
	}
}
