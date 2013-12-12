package de.uni_freiburg.informatik.ultimate.model.location;

import java.io.Serializable;

import de.uni_freiburg.informatik.ultimate.model.boogie.ast.AssertStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.CallStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.EnsuresSpecification;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.LoopInvariantSpecification;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.wrapper.ASTNode;
import de.uni_freiburg.informatik.ultimate.result.Check;

/**
 * Location in a boogie program.
 * @author heizmann@informatik.uni-freiburg.de
 */
public class BoogieLocation implements Serializable, ILocation {
	private static final long serialVersionUID = 4495864682359937328L;

	protected int m_StartLine;
	protected int m_EndLine;
	protected int m_StartColumn;
	protected int m_EndColumn;
	protected String m_FileName;
	
	
	protected ASTNode m_ASTNode;
	
	
	/**
	 * This {@code Location} can be an auxiliary {@code Location} constructed
	 * with respect to some <i>origin</i> {@code Location}. E.g.,
	 * if this is an auxiliary {@code Location} for the else-branch the
	 * <i>origin</i> {@code Location} can be the {@code Location} of an 
	 * if-then-else statement of a program.
	 * 
	 * If this {@code Location} is no auxiliary location the <i>origin</i> is
	 * the location itself.
	 */
	protected ILocation m_Origin;

	private boolean m_LoopEntry;

	
	@SuppressWarnings("unused")
	private BoogieLocation() {
	}


	public BoogieLocation(String fileName, int startLine, int endLine,
												int startColum, int endColumn,
												boolean isLoopEntry) {
		this.m_FileName = fileName;
		this.m_StartLine = startLine;
		this.m_EndLine = endLine;
		this.m_StartColumn = startColum;
		this.m_EndColumn = endColumn;
		this.m_Origin = this;
		this.m_LoopEntry = isLoopEntry;
	}
	
	
	public BoogieLocation(String fileName, int startLine, int endLine,
							int startColum, int endColumn, ILocation origin) {
		this.m_FileName = fileName;
		this.m_StartLine = startLine;
		this.m_EndLine = endLine;
		this.m_StartColumn = startColum;
		this.m_EndColumn = endColumn;
		this.m_Origin = origin;
		this.m_LoopEntry = false;
	}
	
	public BoogieLocation(String fileName, int startLine, int endLine,
			int startColum, int endColumn, ILocation origin, boolean isLoopEntry) {
		this.m_FileName = fileName;
		this.m_StartLine = startLine;
		this.m_EndLine = endLine;
		this.m_StartColumn = startColum;
		this.m_EndColumn = endColumn;
		this.m_Origin = origin;
		this.m_LoopEntry = isLoopEntry;
	}
	

	@Override
	public String toString() {
		return "BPL: "+m_FileName + ":" + m_StartLine + "/" + m_StartColumn + "-"
					+ m_EndLine + "/" + m_EndColumn;
	}

	@Override
	public int getStartLine() {
		return this.m_StartLine;
	}

	@Override
	public int getEndLine() {
		return this.m_EndLine;
	}

	@Override
	public int getStartColumn() {
		return this.m_StartColumn;
	}

	@Override
	public int getEndColumn() {
		return this.m_EndColumn;
	}

	@Override
	public String getFileName() {
		return this.m_FileName;
	}

	@Override
	public ILocation getOrigin() {
		return m_Origin;
	}
	
	@Override
	public Check checkedSpecification() {
		if (m_ASTNode instanceof AssertStatement) {
			return new Check(Check.Spec.ASSERT);
		}
		else if (m_ASTNode instanceof LoopInvariantSpecification) {
			return new Check(Check.Spec.INVARIANT);
		}
		else if (m_ASTNode instanceof CallStatement) {
			return new Check(Check.Spec.PRE_CONDITION);
		}
		else if (m_ASTNode instanceof EnsuresSpecification) {
			return new Check(Check.Spec.POST_CONDITION);
		}
		else if (m_ASTNode == null) {
			throw new NullPointerException();
		}
		else {
			return new Check(Check.Spec.UNKNOWN);
		}

	}
	

	@Override
	public boolean isLoop() {
		return m_LoopEntry;
	}

	public ASTNode getASTNode() {
		return m_ASTNode;
	}


	public void setASTNode(ASTNode aSTNode) {
		m_ASTNode = aSTNode;
	}



}