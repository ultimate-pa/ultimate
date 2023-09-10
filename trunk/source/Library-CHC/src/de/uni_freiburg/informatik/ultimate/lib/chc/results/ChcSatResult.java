/*
 * Copyright (C) 2017 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2014-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2023 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2015-2023 University of Freiburg
 *
 * This file is part of the ULTIMATE CHC Library.
 *
 * The ULTIMATE CHC Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE CHC Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE CHC Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE CHC Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE CHC Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.chc.results;

import de.uni_freiburg.informatik.ultimate.core.model.results.IResult;
import de.uni_freiburg.informatik.ultimate.logic.Model;

/**
 * If a CHC solver (e.g. TreeAutomizer) finds out "SAT", it will report this result.
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 *
 */
public class ChcSatResult implements IResult {

	private final String mPlugin;
	private final String mLongDescription;
	private final Model mModel;

	/**
	 * Create a new result.
	 *
	 * @param plugin
	 *            The ID of the plugin that produced this result.
	 * @param longDescription
	 *            A description of the result.
	 * @param model
	 *            Optionally, a model of the CHC system. Can be null.
	 */
	public ChcSatResult(final String plugin, final String longDescription, final Model model) {
		mPlugin = plugin;
		mLongDescription = longDescription;
		mModel = model;
	}

	@Override
	public String getPlugin() {
		return mPlugin;
	}

	@Override
	public String getShortDescription() {
		return "SAT";
	}

	@Override
	public String getLongDescription() {
		return mLongDescription;
	}

	public Model getModel() {
		return mModel;
	}
}
