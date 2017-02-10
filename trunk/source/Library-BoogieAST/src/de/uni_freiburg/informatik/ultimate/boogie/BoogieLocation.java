/*
 * Copyright (C) 2013-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.boogie;

import java.io.Serializable;

import de.uni_freiburg.informatik.ultimate.boogie.ast.AssertStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BoogieASTNode;
import de.uni_freiburg.informatik.ultimate.boogie.ast.CallStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.EnsuresSpecification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.LoopInvariantSpecification;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.Check;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;

/**
 * Location in a boogie program.
 * 
 * @author heizmann@informatik.uni-freiburg.de
 */
public class BoogieLocation implements Serializable, ILocation {
	private static final long serialVersionUID = 4495864682359937328L;

	protected int mStartLine;
	protected int mEndLine;
	protected int mStartColumn;
	protected int mEndColumn;
	protected String mFileName;

	protected BoogieASTNode mBoogieASTNode;

	private final boolean mLoopEntry;

	public BoogieLocation(final String fileName, final int startLine, final int endLine, final int startColum,
			final int endColumn, final boolean isLoopEntry) {
		mFileName = fileName;
		mStartLine = startLine;
		mEndLine = endLine;
		mStartColumn = startColum;
		mEndColumn = endColumn;
		mLoopEntry = isLoopEntry;
	}

	@Override
	public String toString() {
		return "BPL: " + mFileName + ":" + mStartLine + "/" + mStartColumn + "-" + mEndLine + "/" + mEndColumn;
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
	public String getFileName() {
		return mFileName;
	}

	@Override
	public Check getCheck() {
		if (mBoogieASTNode instanceof AssertStatement) {
			return new Check(Check.Spec.ASSERT);
		} else if (mBoogieASTNode instanceof LoopInvariantSpecification) {
			return new Check(Check.Spec.INVARIANT);
		} else if (mBoogieASTNode instanceof CallStatement) {
			return new Check(Check.Spec.PRE_CONDITION);
		} else if (mBoogieASTNode instanceof EnsuresSpecification) {
			return new Check(Check.Spec.POST_CONDITION);
		} else if (mBoogieASTNode == null) {
			throw new IllegalArgumentException();
		} else {
			return new Check(Check.Spec.UNKNOWN);
		}
	}

	@Override
	public boolean isLoop() {
		return mLoopEntry;
	}

	public BoogieASTNode getBoogieASTNode() {
		return mBoogieASTNode;
	}

	public void setBoogieASTNode(final BoogieASTNode boogieASTNode) {
		mBoogieASTNode = boogieASTNode;
	}
}
