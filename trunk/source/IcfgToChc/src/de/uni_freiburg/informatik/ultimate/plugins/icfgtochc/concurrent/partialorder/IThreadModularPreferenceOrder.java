/*
 * Copyright (C) 2023 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2023 University of Freiburg
 *
 * This file is part of the ULTIMATE IcfgToChc plug-in.
 *
 * The ULTIMATE IcfgToChc plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE IcfgToChc plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE IcfgToChc plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE IcfgToChc plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE IcfgToChc plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.icfgtochc.concurrent.partialorder;

import java.util.Map;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.logic.Term;

public interface IThreadModularPreferenceOrder {
	/**
	 * Constructs a boolean constraint expressing the ordering between two threads. If the constraint evaluates to
	 * {@code true}, then the "lesser" thread is preferred. Otherwise, the "greater" thread is preferred.
	 *
	 * At least one of {@code lesserLoc} and {@code greaterLoc} is guaranteed to be non-null.
	 *
	 * @param lesserLoc
	 *            The location of the thread with a lower thread ID. May be null.
	 * @param lesserLocTerm
	 *            A term denoting the location of the thread with a lower thread ID.
	 * @param greaterLoc
	 *            The location of the thread with a greater thread ID. May be null.
	 * @param greaterLocTerm
	 *            A term denoting the location of the thread with a greater thread ID.
	 * @param locationTerms
	 *            A mapping from locations to the integer value used to represent that location.
	 * @return a constraint over the given terms (including the terms in {@code locationTerms})
	 */
	Term getOrderConstraint(IcfgLocation lesserLoc, Term lesserLocTerm, IcfgLocation greaterLoc, Term greaterLocTerm,
			Map<IcfgLocation, Integer> locationMap);

	boolean isPositional();
}
