/*
 * Copyright (C) 2017 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.epr.dawgs;

import java.util.Collection;
import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.smtinterpol.DefaultLogger;
import de.uni_freiburg.informatik.ultimate.smtinterpol.LogProxy;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprHelpers;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprTheory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.DawgFactory;

public class EprTestHelpers {

	public static EprTheory getEprTheory() {
		return new EprTheoryMock(getLogger());
	}

	public static LogProxy getLogger() {
		return new DefaultLogger();
	}

	public static <LETTER, COLNAMES> void addConstantsWDefaultSort(
			final DawgFactory<LETTER, COLNAMES> dawgFactoryStringString, final Collection<LETTER> constants) {

		for (final LETTER constant : constants) {
			dawgFactoryStringString.addConstant(EprHelpers.getDummySortId(), constant);
		}
	}

	static Collection<String> constantsAbc() {
		final Set<String> constants = new HashSet<String>();
		constants.add("a");
		constants.add("b");
		constants.add("c");
		return constants;
	}

	static Collection<String> constantsAbcde() {
		final Set<String> constants = new HashSet<String>();
		constants.add("a");
		constants.add("b");
		constants.add("c");
		constants.add("d");
		constants.add("e");
		return constants;
	}
}
