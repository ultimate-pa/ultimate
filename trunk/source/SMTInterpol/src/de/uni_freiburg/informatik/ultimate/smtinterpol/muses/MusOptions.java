/*
 * Copyright (C) 2020 Leonard Fichtner
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
package de.uni_freiburg.informatik.ultimate.smtinterpol.muses;

/**
 * Defines the additional options used by the MusEnumerationScript.
 *
 * @author LeonardFichtner
 *
 */
public interface MusOptions {

	public String INTERPOLATION_HEURISTIC = ":interpolation-heuristic";
	public String TOLERANCE = ":tolerance";
	public String ENUMERATION_TIMEOUT = ":enumeration-timeout";
	public String HEURISTIC_TIMEOUT = ":heuristic-timeout";
	public String LOG_ADDITIONAL_INFORMATION = ":log-additional-information";
	public String UNKNOWN_ALLOWED = ":unknown-allowed";
}
