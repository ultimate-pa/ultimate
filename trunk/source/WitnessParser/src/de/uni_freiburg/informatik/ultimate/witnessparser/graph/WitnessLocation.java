/*
 * Copyright (C) 2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE WitnessParser plug-in.
 * 
 * The ULTIMATE WitnessParser plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE WitnessParser plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE WitnessParser plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE WitnessParser plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE WitnessParser plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.witnessparser.graph;

import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.Check;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;

public class WitnessLocation implements ILocation {

	private final String mFilename;
	private final int mStartLine;
	private int mEndLine;
	private final int mStartColumn;
	private final int mEndColumn;

	public WitnessLocation(final String filename, final int startline) {
		this(filename, startline, startline);
	}

	public WitnessLocation(final String filename, final int startline, final int endline) {
		mFilename = filename;
		mStartLine = startline;
		if (endline == -1) {
			mEndLine = startline;
		} else {
			mEndLine = endline;
		}
		mStartColumn = -1;
		mEndColumn = -1;
	}

	@Override
	public String getFileName() {
		return mFilename;
	}

	@Override
	public int getStartLine() {
		return mStartLine;
	}

	@Override
	public int getEndLine() {
		return mEndLine;
	}

	@Override
	public int getStartColumn() {
		return mStartColumn;
	}

	@Override
	public int getEndColumn() {
		return mEndColumn;
	}

	@Override
	public Check getCheck() {
		throw new UnsupportedOperationException();
	}

	@Override
	public boolean isLoop() {
		throw new UnsupportedOperationException();
	}

}
