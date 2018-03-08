/*
 * Copyright (C) 2017 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.core.lib.models.annotation;

import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;

/**
 * A default implementation of the {@link ILocation} interface. Does not support the deprecated parts of
 * {@link ILocation}.
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class DefaultLocation extends ModernAnnotations implements ILocation {

	private static final long serialVersionUID = -3997424074261758149L;
	private final String mFilename;
	private final int mStartLine;
	private final int mEndLine;
	private final int mStartColumn;
	private final int mEndColumn;

	/**
	 * Create a "dummy" location without meaningful information.
	 */
	public DefaultLocation() {
		this(null, -1, -1, -1, -1);
	}

	/**
	 * Create a {@link DefaultLocation} with meaningful values.
	 *
	 * @param fileName
	 * @param startLine
	 * @param endLine
	 * @param startColum
	 * @param endColumn
	 */
	public DefaultLocation(final String fileName, final int startLine, final int endLine, final int startColum,
			final int endColumn) {
		mFilename = fileName;
		mStartLine = startLine;
		mEndLine = endLine;
		mStartColumn = startColum;
		mEndColumn = endColumn;
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
	public String toString() {
		final StringBuilder sb = new StringBuilder();
		sb.append("DFL: ");
		sb.append(" [L");
		if (getStartLine() == getEndLine()) {
			sb.append(getStartLine());
		} else {
			sb.append(getStartLine());
			sb.append("-");
			sb.append(getEndLine());
		}
		sb.append("]");
		return sb.toString();
	}
}
