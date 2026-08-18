/*
 * Copyright (C) 2026 Dominik Klumpp (klumpp@lix.polytechnique.fr)
 * Copyright (C) 2026 École Polytechnique
 *
 * This file is part of the ULTIMATE Civlizer plug-in.
 *
 * The ULTIMATE Civlizer plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Civlizer plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Civlizer plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Civlizer plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Civlizer plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.civlizer.results;

import de.uni_freiburg.informatik.ultimate.civlizer.Activator;
import de.uni_freiburg.informatik.ultimate.core.model.results.IResult;

public class CivlSuccessResult implements IResult {
	private final String mSuccessMessage;

	public CivlSuccessResult(final String successMessage) {
		mSuccessMessage = successMessage;
	}

	@Override
	public String getPlugin() {
		return Activator.PLUGIN_ID;
	}

	@Override
	public String getShortDescription() {
		return "The Civl-ized program was successfully verified by Civl.";
	}

	@Override
	public String getLongDescription() {
		return mSuccessMessage;
	}
}
