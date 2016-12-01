/*
 * Copyright (C) 2016 University of Freiburg
 *
 * This file is part of the Ultimate Delta Debugger plug-in.
 *
 * The Ultimate Delta Debugger plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The Ultimate Delta Debugger plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the Ultimate Delta Debugger plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the Ultimate Delta Debugger plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the Ultimate Delta Debugger plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.deltadebugger.core.passes;

import de.uni_freiburg.informatik.ultimate.deltadebugger.core.PassDescription;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.generators.hdd.AggressiveStrategy;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.generators.hdd.HddGeneratorFactory;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.generators.hdd.IHddStrategy;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.generators.hdd.SafeStrategy;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.generators.hdd.UnreferencedStrategy;

/**
 * HDD default Passes.
 */
public final class HddPass {

	public static final IHddStrategy AGGRESSIVE_STRATEGY = new AggressiveStrategy();
	public static final IHddStrategy SAFE_STRATEGY = new SafeStrategy();
	public static final IHddStrategy UNREFERENCED_STRATEGY = new UnreferencedStrategy();

	public static final IHddStrategy DEFAULT_STRATEGY = AGGRESSIVE_STRATEGY;

	/**
	 * Single-Pass HDD algorithm (without reparsing between levels).
	 */
	public static final PassDescription DEFAULT = PassDescription
			.builder(new HddGeneratorFactory(DEFAULT_STRATEGY, false)::analyze).name("HDD")
			.description("Hiearchical Delta-Debugging inspired pass without reparsing between levels").build();

	/**
	 * Single-Pass HDD algorithm (with reparsing between levels).
	 */
	public static final PassDescription REPARSING = PassDescription
			.builder(new HddGeneratorFactory(DEFAULT_STRATEGY, true)::analyze).name("HDD (Reparsing)")
			.description("Hiearchical Delta-Debugging inspired pass with reparsing between levels").build();

	/**
	 * Repeat until no redcution is possible (HDD*).
	 */
	public static final PassDescription HDDSTAR = DEFAULT.copy().repeatUntilReductionFails(true).build();

	private HddPass() {
	}
}
