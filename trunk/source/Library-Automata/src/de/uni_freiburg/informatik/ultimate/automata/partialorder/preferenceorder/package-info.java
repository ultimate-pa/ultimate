/*
 * Copyright (C) 2025 Emma Bach
 * Copyright (C) 2025 Marcel Ebbinghaus
 * Copyright (C) 2025 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2025 University of Freiburg
 *
 * This file is part of the ULTIMATE Automata Library.
 *
 * The ULTIMATE Automata Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Automata Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Automata Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Automata Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Automata Library grant you additional permission
 * to convey the resulting work.
 */

/**
 * This package contains classes for constructing monitor-based positional lexicographic preference orders, as
 * represented by the interface
 * {@link de.uni_freiburg.informatik.ultimate.automata.partialorder.preferenceorder.IPreferenceOrder}.
 *
 * Preference orders are used in partial order reduction to select which representatives should be included in a
 * reduction, which can be crucial for algorithms working with the reduction. For instance, in verification (such as
 * GemCutter's use of TraceAbstraction), it can determine whether or not the proof of the reduction is simple enough
 * such that it can be found automatically.
 *
 * As they play such a crucial role, care must be taken to use a suitable preference order for a problem. This package
 * aims to provide users with a large space of choices, by defining various operators with which preference orders can
 * be composed from simpler preference orders.
 */
package de.uni_freiburg.informatik.ultimate.automata.partialorder.preferenceorder;
