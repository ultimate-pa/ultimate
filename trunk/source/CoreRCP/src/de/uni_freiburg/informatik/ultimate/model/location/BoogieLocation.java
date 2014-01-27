package de.uni_freiburg.informatik.ultimate.model.location;

import java.io.Serializable;

import de.uni_freiburg.informatik.ultimate.model.boogie.ast.AssertStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BoogieASTNode;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.CallStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.EnsuresSpecification;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.LoopInvariantSpecification;
import de.uni_freiburg.informatik.ultimate.result.Check;

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

	/**
	 * This {@code Location} can be an auxiliary {@code Location} constructed
	 * with respect to some <i>origin</i> {@code Location}. E.g., if this is an
	 * auxiliary {@code Location} for the else-branch the <i>origin</i>
	 * {@code Location} can be the {@code Location} of an if-then-else statement
	 * of a program.
	 * 
	 * If this {@code Location} is no auxiliary location the <i>origin</i> is
	 * the location itself.
	 */
	protected ILocation mOrigin;

	private boolean mLoopEntry;

	@SuppressWarnings("unused")
	private BoogieLocation() {
	}

	public BoogieLocation(String fileName, int startLine, int endLine,
			int startColum, int endColumn, boolean isLoopEntry) {
		this.mFileName = fileName;
		this.mStartLine = startLine;
		this.mEndLine = endLine;
		this.mStartColumn = startColum;
		this.mEndColumn = endColumn;
		this.mOrigin = this;
		this.mLoopEntry = isLoopEntry;
	}

	public BoogieLocation(String fileName, int startLine, int endLine,
			int startColum, int endColumn, ILocation origin) {
		this.mFileName = fileName;
		this.mStartLine = startLine;
		this.mEndLine = endLine;
		this.mStartColumn = startColum;
		this.mEndColumn = endColumn;
		this.mOrigin = origin;
		this.mLoopEntry = false;
	}

	public BoogieLocation(String fileName, int startLine, int endLine,
			int startColum, int endColumn, ILocation origin, boolean isLoopEntry) {
		this.mFileName = fileName;
		this.mStartLine = startLine;
		this.mEndLine = endLine;
		this.mStartColumn = startColum;
		this.mEndColumn = endColumn;
		this.mOrigin = origin;
		this.mLoopEntry = isLoopEntry;
	}

	@Override
	public String toString() {
		return "BPL: " + mFileName + ":" + mStartLine + "/" + mStartColumn
				+ "-" + mEndLine + "/" + mEndColumn;
	}

	@Override
	public int getStartLine() {
		return this.mStartLine;
	}

	@Override
	public int getEndLine() {
		return this.mEndLine;
	}

	@Override
	public int getStartColumn() {
		return this.mStartColumn;
	}

	@Override
	public int getEndColumn() {
		return this.mEndColumn;
	}

	@Override
	public String getFileName() {
		return this.mFileName;
	}

	@Override
	public ILocation getOrigin() {
		return mOrigin;
	}

	@Override
	public Check checkedSpecification() {
		if (mBoogieASTNode instanceof AssertStatement) {
			return new Check(Check.Spec.ASSERT);
		} else if (mBoogieASTNode instanceof LoopInvariantSpecification) {
			return new Check(Check.Spec.INVARIANT);
		} else if (mBoogieASTNode instanceof CallStatement) {
			return new Check(Check.Spec.PRE_CONDITION);
		} else if (mBoogieASTNode instanceof EnsuresSpecification) {
			return new Check(Check.Spec.POST_CONDITION);
		} else if (mBoogieASTNode == null) {
			throw new NullPointerException();
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

	public void setBoogieASTNode(BoogieASTNode BoogieASTNode) {
		mBoogieASTNode = BoogieASTNode;
	}

}