/*
 * Copyright (C) 2013-2015 Betim Musa (musab@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE AutomataScriptParser plug-in.
 * 
 * The ULTIMATE AutomataScriptParser plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE AutomataScriptParser plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE AutomataScriptParser plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE AutomataScriptParser plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE AutomataScriptParser plug-in grant you additional permission
 * to convey the resulting work.
 */
/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser;

import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.Check;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;

/**
 * 
 * Location for AutomataScript files.
 * 
 * @author musab@informatik.uni-freiburg.de
 *
 */
public class AutomataScriptLocation implements ILocation {
	protected int mStartLine;
	protected int mEndLine;
	protected int mStartColumn;
	protected int mEndColumn;
	protected String mFileName;

	public AutomataScriptLocation(final String filename, final int startline, final int endLine, final int startColumn,
			final int endColumn) {
		mStartLine = startline;
		mEndLine = endLine;
		mStartColumn = startColumn;
		mEndColumn = endColumn;
		mFileName = filename;
	}

	public AutomataScriptLocation(final String fileName) {
		mFileName = fileName;
	}

	public AutomataScriptLocation(final int startLine, final int endLine) {
		mStartLine = startLine;
		mEndLine = endLine;
	}

	@Override
	public String toString() {
		final StringBuilder builder = new StringBuilder();
		builder.append("Location: File \"");
		builder.append(mFileName);
		builder.append("\" at Line: ");
		builder.append(mStartLine);
		builder.append(", Col: ");
		builder.append(mStartColumn);
		return builder.toString();
	}

	@Override
	public String getFileName() {
		return mFileName;
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
