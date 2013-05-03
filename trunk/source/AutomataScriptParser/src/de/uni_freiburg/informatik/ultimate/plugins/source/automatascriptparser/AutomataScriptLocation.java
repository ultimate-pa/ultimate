/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser;

import de.uni_freiburg.informatik.ultimate.model.ILocation;
import de.uni_freiburg.informatik.ultimate.result.Check;

/**
 * 
 * Location for AutomataScript files.
 * @author musab@informatik.uni-freiburg.de
 *
 */
public class AutomataScriptLocation implements ILocation {
	protected int m_StartLine;
	protected int m_EndLine;
	protected int m_StartColumn;
	protected int m_EndColumn;
	protected String m_FileName;
	
	
	
	public AutomataScriptLocation(String m_FileName, int m_StartLine, int m_EndLine,
			int m_StartColumn, int m_EndColumn) {
		this.m_StartLine = m_StartLine;
		this.m_EndLine = m_EndLine;
		this.m_StartColumn = m_StartColumn;
		this.m_EndColumn = m_EndColumn;
		this.m_FileName = m_FileName;
	}

	public AutomataScriptLocation(String m_FileName) {
		this.m_FileName = m_FileName;
	}


	public AutomataScriptLocation(int m_StartLine, int m_EndLine) {
		this.m_StartLine = m_StartLine;
		this.m_EndLine = m_EndLine;
	}
	
	





	@Override
	public String toString() {
		StringBuilder builder = new StringBuilder();
		builder.append("Location: File \"");
		builder.append(m_FileName);
		builder.append("\" at Line: ");
		builder.append(m_StartLine);
		builder.append(", Col: ");
		builder.append(m_StartColumn);
//		
//		builder.append(", Endline: ");
//		builder.append(m_EndLine);
//		builder.append(", EndCol: ");
//		builder.append(m_EndColumn);
//	
		return builder.toString();
	}





	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.model.ILocation#getFileName()
	 */
	@Override
	public String getFileName() {
		// TODO Auto-generated method stub
		return m_FileName;
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.model.ILocation#getStartLine()
	 */
	@Override
	public int getStartLine() {
		// TODO Auto-generated method stub
		return m_StartLine;
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.model.ILocation#getEndLine()
	 */
	@Override
	public int getEndLine() {
		// TODO Auto-generated method stub
		return m_EndLine;
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.model.ILocation#getStartColumn()
	 */
	@Override
	public int getStartColumn() {
		// TODO Auto-generated method stub
		return m_StartColumn;
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.model.ILocation#getEndColumn()
	 */
	@Override
	public int getEndColumn() {
		// TODO Auto-generated method stub
		return m_EndColumn;
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.model.ILocation#getOrigin()
	 */
	@Override
	public ILocation getOrigin() {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException();
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.model.ILocation#checkedSpecification()
	 */
	@Override
	public Check checkedSpecification() {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException();
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.model.ILocation#isLoop()
	 */
	@Override
	public boolean isLoop() {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException();
	}

}
