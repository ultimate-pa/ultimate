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

import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.DefaultLocation;

/**
 * 
 * Location for AutomataScript files.
 * 
 * @author musab@informatik.uni-freiburg.de
 *
 */
public class AutomataScriptLocation extends DefaultLocation {

	private static final long serialVersionUID = -236140718161674236L;

	public AutomataScriptLocation(final String filename, final int startline, final int endLine, final int startColumn,
			final int endColumn) {
		super(filename, startline, endLine, startColumn, endColumn);
	}

	public AutomataScriptLocation(final String fileName) {
		this(fileName, 0, 0, 0, 0);
	}

	public AutomataScriptLocation(final int startLine, final int endLine) {
		this(null, startLine, endLine, 0, 0);
	}

	@Override
	public String toString() {
		final StringBuilder builder = new StringBuilder();
		builder.append("Location: File \"");
		builder.append(getFileName());
		builder.append("\" at Line: ");
		builder.append(getStartLine());
		builder.append(", Col: ");
		builder.append(getStartColumn());
		return builder.toString();
	}
}
