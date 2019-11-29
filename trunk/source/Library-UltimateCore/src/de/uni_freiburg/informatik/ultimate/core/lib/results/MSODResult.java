/*
 * Copyright (C) 2019 Elisabeth Henkel (henkele@informatik.uni-freiburg.de)
 * Copyright (C) 2019 Nico Hauff (hauffn@informatik.uni-freiburg.de)
 * Copyright (C) 2019 University of Freiburg
 *
 * This file is part of the ULTIMATE Core.
 *
 * The ULTIMATE Core is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Core is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Core. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Core, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Core grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.core.lib.results;

import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;

/**
 * Object for results of {@link MSODSolver} class.
 *
 * @author hauffn@informatik.uni-freiburg.de
 * @author henkele@informatik.uni-freiburg.de
 */
public class MSODResult extends GenericResult {
	private final LBool mValue;

	public MSODResult(final String plugin, final String shortDescription, final String longDescription,
			final LBool value, final Severity severity) {

		super(plugin, shortDescription, longDescription, severity);
		mValue = value;
	}

	public LBool getValue() {
		return mValue;
	}
}