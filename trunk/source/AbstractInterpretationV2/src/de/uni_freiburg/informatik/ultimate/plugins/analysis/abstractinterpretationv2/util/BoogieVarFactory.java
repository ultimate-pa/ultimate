/*
 * Copyright (C) 2017 Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
 *
 * This file is part of the ULTIMATE AbstractInterpretationV2 plug-in.
 *
 * The ULTIMATE AbstractInterpretationV2 plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE AbstractInterpretationV2 plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE AbstractInterpretationV2 plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE AbstractInterpretationV2 plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE AbstractInterpretationV2 plug-in grant you additional permission
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.util;

import java.util.HashMap;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.logic.Sort;

/**
 * A factory to create BoogieVar's with unique names
 *
 * @author Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 *
 */
public class BoogieVarFactory {
	private final ManagedScript mManagedScript;
	private final Map<String, Integer> mIndices;

	public BoogieVarFactory(final ManagedScript managedScript) {
		mManagedScript = managedScript;
		mIndices = new HashMap<>();
	}

	public TemporaryBoogieVar createFreshBoogieVar(final String basename, final Sort sort) {
		final int idx = mIndices.getOrDefault(basename, 0);
		final String name = basename + "_" + idx;
		mIndices.put(basename, idx + 1);
		return new TemporaryBoogieVar(name, sort, mManagedScript);
	}
}
