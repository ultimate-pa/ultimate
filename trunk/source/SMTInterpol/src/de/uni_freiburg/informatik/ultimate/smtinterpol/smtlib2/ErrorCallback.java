/*
 * Copyright (C) 2020 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2;

/**
 * Interface that SMTInterpol an use to notify about different internal
 * problems. This is useful for delta debugging, where we want to find
 * benchmarks with the same problem.
 *
 * @author Jochen Hoenicke
 */
public interface ErrorCallback {
	public enum ErrorReason {
		INVALID_MODEL, INVALID_PROOF, EXCEPTION_ON_ASSERT, EXCEPTION_ON_CHECKSAT, ERROR_ON_POP, CHECKSAT_STATUS_DIFFERS,
		ERROR_ON_GET_INTERPOLANTS, GET_MODEL_BUT_UNSAT, GET_MODEL_BUT_UNKNOWN, GET_PROOF_BUT_SAT,
	};

	public void notifyError(ErrorReason reason);
}
