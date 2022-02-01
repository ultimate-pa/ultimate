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

import java.util.Objects;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.debugidentifiers.DebugIdentifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.debugidentifiers.DuplicatedDebugIdentifier;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.BoogieIcfgLocation;

/**
 *
 * @author dietsch@informatik.uni-freiburg.de
 *
 */
public final class ProductLocationNameGenerator {

	private static final String NONWA = "NONWA";
	private int mHelperUnifique;

	protected ProductLocationNameGenerator() {
		mHelperUnifique = 0;
	}

	protected static DebugIdentifier generateStateName(final BoogieIcfgLocation loc) {
		return generateStateName(loc, null);
	}

	/**
	 * Central method to create the product state's debug identifier.
	 *
	 * @param rcfgName
	 *            Name of the state in the RCFG
	 * @param nwaName
	 *            Name of the state in the BA / NWA
	 * @return a String representing the name of this location in the product
	 */
	protected static DebugIdentifier generateStateName(final BoogieIcfgLocation loc, final String nwaName) {
		if (nwaName == null) {
			return new BuchiProgramDebugIdentifier(loc, NONWA);
		}
		return new BuchiProgramDebugIdentifier(loc, nwaName);
	}

	protected DebugIdentifier generateHelperStateName(final DebugIdentifier location) {
		mHelperUnifique++;
		if (mHelperUnifique < 0) {
			throw new IllegalArgumentException();
		}
		return new BuchiProgramHelperStateDebugIdentifier(location, mHelperUnifique);
	}

	protected static boolean isHelperState(final BoogieIcfgLocation loc) {
		if (loc == null) {
			return false;
		}
		return loc.getDebugIdentifier() instanceof BuchiProgramHelperStateDebugIdentifier;
	}

	private static final class BuchiProgramDebugIdentifier extends DebugIdentifier {

		private final int mIcfgHashcode;
		private final DebugIdentifier mIcfgIdentifier;
		private final String mNwaLocation;

		public BuchiProgramDebugIdentifier(final BoogieIcfgLocation loc, final String nwaLocation) {
			mIcfgIdentifier = Objects.requireNonNull(loc).getDebugIdentifier();
			mIcfgHashcode = loc.hashCode();
			mNwaLocation = Objects.requireNonNull(nwaLocation);
		}

		@Override
		public String toString() {
			return mIcfgIdentifier.toString() + "_" + mNwaLocation;
		}

		@Override
		public int hashCode() {
			final int prime = 31;
			int result = 1;
			result = prime * result + mIcfgHashcode;
			result = prime * result + mNwaLocation.hashCode();
			return result;
		}

		@Override
		public boolean equals(final Object obj) {
			if (this == obj) {
				return true;
			}
			if (obj == null) {
				return false;
			}
			if (getClass() != obj.getClass()) {
				return false;
			}
			final BuchiProgramDebugIdentifier other = (BuchiProgramDebugIdentifier) obj;
			if (mIcfgHashcode != other.mIcfgHashcode) {
				return false;
			}
			if (!mNwaLocation.equals(other.mNwaLocation)) {
				return false;
			}
			return true;
		}

	}

	private static final class BuchiProgramHelperStateDebugIdentifier extends DuplicatedDebugIdentifier {

		public BuchiProgramHelperStateDebugIdentifier(final DebugIdentifier debugIdentifier, final int duplication) {
			super(debugIdentifier, duplication);
		}
	}

}
