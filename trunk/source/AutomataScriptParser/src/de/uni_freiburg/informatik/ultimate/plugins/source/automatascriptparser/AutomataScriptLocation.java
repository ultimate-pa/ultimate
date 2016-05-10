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

import de.uni_freiburg.informatik.ultimate.models.ILocation;
import de.uni_freiburg.informatik.ultimate.models.annotation.Check;

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
	public Check getCheck() {
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
