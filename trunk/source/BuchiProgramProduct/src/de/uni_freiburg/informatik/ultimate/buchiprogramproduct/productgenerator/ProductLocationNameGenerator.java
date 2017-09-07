/*
 * Copyright (C) 2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE BuchiProgramProduct plug-in.
 *
 * The ULTIMATE BuchiProgramProduct plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE BuchiProgramProduct plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE BuchiProgramProduct plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE BuchiProgramProduct plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE BuchiProgramProduct plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.buchiprogramproduct.productgenerator;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.BoogieIcfgLocation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;

/**
 *
 * @author dietsch@informatik.uni-freiburg.de
 *
 */
public final class ProductLocationNameGenerator {

	private static final String HELPER_STATE_PREFIX = "crhelper";
	private int mHelperUnifique;
	private final INwaOutgoingLetterAndTransitionProvider<CodeBlock, String> mNWA;

	protected ProductLocationNameGenerator(final INwaOutgoingLetterAndTransitionProvider<CodeBlock, String> nwa) {
		assert nwa != null;

		mHelperUnifique = 0;
		mNWA = nwa;
	}

	protected String generateStateName(final BoogieIcfgLocation loc) {
		return generateStateName(loc, null);
	}

	/**
	 * Central method to create the product state's names.
	 *
	 * @param rcfgName
	 *            Name of the state in the RCFG
	 * @param nwaName
	 *            Name of the state in the BA / NWA
	 * @return a String representing the name of this location in the product
	 */
	protected String generateStateName(final BoogieIcfgLocation loc, final String nwaName) {
		return generateStateName(String.valueOf(loc.hashCode()) + '_' + loc.getDebugIdentifier(), nwaName);
	}

	private String generateStateName(final String rcfgName, final String nwaName) {
		assert nwaName == null || !nwaName.isEmpty();
		if (nwaName == null) {
			return "NP" + "__" + rcfgName;
		} else if (rcfgName.equals("ULTIMATE.startENTRY") && mNWA.isInitial(nwaName)) {
			return "ULTIMATE.start";
		} else {
			return rcfgName + "__" + nwaName;
		}
	}

	protected String generateHelperStateName(final String location) {
		mHelperUnifique++;
		return HELPER_STATE_PREFIX + Integer.toString(mHelperUnifique) + "__" + location;
	}

	protected static boolean isHelperState(final BoogieIcfgLocation loc) {
		if (loc == null) {
			return false;
		}
		return loc.getDebugIdentifier().startsWith(HELPER_STATE_PREFIX);
	}

}
