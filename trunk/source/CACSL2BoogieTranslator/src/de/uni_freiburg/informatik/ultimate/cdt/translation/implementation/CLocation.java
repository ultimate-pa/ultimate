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
package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation;

import org.eclipse.cdt.core.dom.ast.IASTNode;

import de.uni_freiburg.informatik.ultimate.models.annotation.Check;

public class CLocation extends CACSLLocation {

	private static final long serialVersionUID = -7497131349540138810L;
	private final IASTNode mNode;

	protected CLocation(IASTNode node, Check checkedSpec, boolean ignoreDuringBacktranslation) {
		super(checkedSpec, ignoreDuringBacktranslation);
		mNode = node;
	}

	@Override
	public String getFileName() {
		if (mNode != null) {
			return mNode.getFileLocation().getFileName();
		}
		return null;
	}

	@Override
	public int getStartLine() {
		if (mNode != null) {
			return mNode.getFileLocation().getStartingLineNumber();
		}
		return -1;
	}

	@Override
	public int getEndLine() {
		if (mNode != null) {
			return mNode.getFileLocation().getEndingLineNumber();
		}
		return -1;
	}

	@Override
	public int getStartColumn() {
		return -1;
	}

	@Override
	public int getEndColumn() {
		return -1;
	}

	@Override
	public boolean isLoop() {
		return false;
	}

	public IASTNode getNode() {
		return mNode;
	}

	@Override
	public String toString() {
		StringBuilder sb = new StringBuilder();
		if (mNode != null) {
			sb.append("C: ");
			sb.append(mNode.getRawSignature());
			sb.append(" [");
			if (getStartLine() == getEndLine()) {
				sb.append(getStartLine());
			} else {
				sb.append(getStartLine());
				sb.append("-");
				sb.append(getEndLine());
			}
			sb.append("]");
		}

		return sb.toString();
	}

}
