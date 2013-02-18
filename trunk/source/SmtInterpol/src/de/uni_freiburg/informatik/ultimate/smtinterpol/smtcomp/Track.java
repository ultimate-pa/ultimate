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
package de.uni_freiburg.informatik.ultimate.smtinterpol.smtcomp;

public enum Track {
	MAIN(false, false, null, null),
	APPLICATION(true, false, ":print-success", "true"),
	UNSAT_CORE(false, true, ":produce-unsat-cores", "true"),
	PROOF_GEN(false, false, ":produce-proofs", "true");
	Track(boolean ppAllowed, boolean namedAllowed, String io, String iov) {
		m_PushPopAllowed = ppAllowed;
		m_NamedAllowed = namedAllowed;
		m_InitialOption = io;
		m_InitialOptionValue = iov;
	}
	public boolean isPushPopAllowed() {
		return m_PushPopAllowed;
	}
	public boolean isNamedAllowed() {
		return m_NamedAllowed;
	}
	public boolean hasInitalOption() {
		return m_InitialOption != null;
	}
	public String getInitialOption() {
		return m_InitialOption;
	}
	public String getInitialOptionValue() {
		return m_InitialOptionValue;
	}
	private boolean m_PushPopAllowed;
	private boolean m_NamedAllowed;
	private String m_InitialOption;
	private String m_InitialOptionValue;
}
