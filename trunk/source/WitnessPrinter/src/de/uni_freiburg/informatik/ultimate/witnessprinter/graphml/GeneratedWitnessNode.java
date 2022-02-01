/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE CACSL2BoogieTranslator plug-in.
 *
 * The ULTIMATE CACSL2BoogieTranslator plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE CACSL2BoogieTranslator plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE CACSL2BoogieTranslator plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE CACSL2BoogieTranslator plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE CACSL2BoogieTranslator plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.witnessprinter.graphml;

/**
 *
 * @author dietsch@informatik.uni-freiburg.de
 *
 */
public class GeneratedWitnessNode {
	private final boolean mIsEntry;
	private final String mId;
	private final boolean mIsError;
	private final boolean mIsSink;
	private String mInvariant;
	private final boolean mIsHonda;

	GeneratedWitnessNode(final long currentNodeId, final boolean isEntry, final boolean isError, final boolean isSink,
			final boolean isHonda) {
		mIsEntry = isEntry;
		mIsError = isError;
		mId = 'N' + String.valueOf(currentNodeId);
		mIsSink = isSink;
		mIsHonda = isHonda;
		mInvariant = null;
	}

	public boolean isEntry() {
		return mIsEntry;
	}

	public boolean isError() {
		return mIsError;
	}

	public boolean isSink() {
		return mIsSink;
	}

	public String getName() {
		return mId;
	}

	public String getInvariant() {
		return mInvariant;
	}

	public void setInvariant(final String invariant) {
		mInvariant = invariant;
	}

	@Override
	public String toString() {
		return mId;
	}

	public boolean isHonda() {
		return mIsHonda;
	}
}
