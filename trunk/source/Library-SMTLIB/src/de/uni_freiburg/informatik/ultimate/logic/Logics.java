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

/**
 * All logics configured in SMTLIB.
 * @author Juergen Christ
 */
public enum Logics {
	CORE,// Pure Boolean logic
	AUFLIA,
	AUFLIRA,
	AUFNIRA,
	LRA,
	QF_ABV,
	QF_AUFBV,
	QF_AUFLIA,
	QF_AX,
	QF_BV,
	QF_IDL,
	QF_LIA,
	QF_LRA,
	QF_NIA,
	QF_NRA,
	QF_RDL,
	QF_UF,
	QF_UFBV,
	QF_UFIDL,
	QF_UFLIA,
	QF_UFLRA,
	// This logic is SMTInterpol specific and captures the cominbation UF, LIA,
	// and LRA
	QF_UFLIRA,
	QF_UFNRA,
	UFLRA,
	UFNIA;
	/**
	 * Is this logic mixed integer and real?
	 * @return <code>true</code> if and only if mixed arithmetic can be used in
	 *         this logic.
	 */
	public boolean isIRA() {
		return this == AUFLIRA || this == AUFNIRA || this == QF_UFLIRA;
	}
	/**
	 * Does this logic support uninterpreted functions and sorts?
	 * @return <code>true</code> if and only if the logic supports uninterpreted
	 *         functions and sorts.
	 */
	@SuppressWarnings("incomplete-switch")
	public boolean isUF() {
		switch (this) { // NOCHECKSTYLE
		case AUFLIA:
		case AUFLIRA:
		case AUFNIRA:
		case QF_AUFBV:
		case QF_AUFLIA:
		case QF_UF:
		case QF_UFBV:
		case QF_UFIDL:
		case QF_UFLIA:
		case QF_UFLRA:
		case QF_UFLIRA:
		case QF_UFNRA:
		case UFLRA:
		case UFNIA:
			return true;
		}
		return false;
	}
	/**
	 * Does this logic support arrays?
	 * @return <code>true</code> if and only if this logic supports arrays.
	 */
	@SuppressWarnings("incomplete-switch")
	public boolean isArray() {
		switch (this) { // NOCHECKSTYLE
		case AUFLIA:
		case AUFLIRA:
		case AUFNIRA:
		case QF_AX:
		case QF_ABV:
		case QF_AUFBV:
		case QF_AUFLIA:
			return true;
		}
		return false;
	}
	/**
	 * Does this logic support quantifiers?
	 * @return <code>true</code> if and only if quantified formulas can be build
	 *         in this logic.
	 */
	@SuppressWarnings("incomplete-switch")
	public boolean isQuantified() {
		switch (this) { // NOCHECKSTYLE
		case AUFLIA:
		case AUFLIRA:
		case AUFNIRA:
		case LRA:
		case UFLRA:
		case UFNIA:
			return true;
		}
		return false;
	}
}
