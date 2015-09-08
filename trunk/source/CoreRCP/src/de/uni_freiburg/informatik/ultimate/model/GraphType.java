/*
 * Copyright (C) 2008-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2010-2015 Jürgen Christ (christj@informatik.uni-freiburg.de)
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
/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.model;

import java.io.File;
import java.io.Serializable;
import java.text.DateFormat;
import java.text.SimpleDateFormat;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Date;
import java.util.List;

import org.eclipse.core.runtime.Assert;

import de.uni_freiburg.informatik.ultimate.plugins.Constants;

/**
 * Intended for separating different types of graphs and trees like Call Graphs,
 * Data Flow Graphs, AST Should also specify their special attributes
 * 
 * Change in Ultimate 2.0:
 * 
 * A GraphType should be identified by its String representation. Unlike object
 * identity this should be preserved during serialization. Therefore the equals
 * method now checks for equal String representation instead of object identity.
 * In order to be consistent this change is carried to hashCode.
 * 
 * The changes will allow the GraphType to remain a suitable key in the model
 * managers in-memory map and its string representation to be the key in the
 * repository.
 * 
 * @author dietsch
 */
public class GraphType implements Serializable {

	/**
	 * long serialVersionUID
	 */
	private static final long serialVersionUID = -2922069733243189149L;

	private int m_Size;

	private String m_Creator;
	private Date m_Created;
	private long m_LastModified;
	private String m_LastModifier;
	private Type m_Type;
	private int m_Iteration;
	private boolean m_Touched;
	private List<String> m_FileNames;
	private DateFormat m_LastModifiedStringFormat;

	private boolean m_IsCyclic;
	private boolean m_IsDirected;
	private boolean m_IsTree;
	private boolean m_IsOrdered;
	private boolean m_IsMultiGraph;
	private boolean m_IsFinite;

	/**
	 * @author dietsch
	 */
	public enum Type {
		AST, CG, CFG, DFG, CST, TS, PG, OTHER
	}

	public GraphType(String creatorPluginID, Type type, Collection<String> fileNames) {
		Assert.isNotNull(fileNames);
		Assert.isNotNull(type);
		m_Creator = creatorPluginID;
		m_Type = type;
		m_FileNames = new ArrayList<String>(fileNames);

		init();
	}

	public GraphType(String creatorPluginID, String type, List<String> fileNames) throws Exception {
		Assert.isNotNull(fileNames);
		Assert.isNotNull(type);
		this.m_Creator = creatorPluginID;
		this.m_FileNames = fileNames;
		this.m_Type = Type.OTHER;
		init();
	}

	/**
	 * Should be set AFTER a write operation was performed on this data
	 * structure was completed
	 * 
	 * @param modifierPluginID
	 *            The ID of the plugin which performed the write operation
	 */
	public void modified(String modifierPluginID) {
		this.setDirty(true);
		this.m_LastModifier = modifierPluginID;
		this.m_LastModified = System.currentTimeMillis();
		this.m_Iteration++;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see java.lang.Object#equals(java.lang.Object)
	 */
	@Override
	public boolean equals(Object obj) {
		if (obj instanceof GraphType) {
			GraphType t = (GraphType) obj;
			return t.m_LastModified == m_LastModified && t.m_Creator.equals(m_Creator);
		}
		return false;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see java.lang.Object#hashCode()
	 */
	@Override
	public int hashCode() {
		return (int) m_LastModified;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see java.lang.Object#toString()
	 */
	public String toString() {
		StringBuffer sb = new StringBuffer();
		for (String fileName : this.m_FileNames) {
			sb.append(new File(fileName).getName());
		}
		if (sb.length() > 0) {
			sb.append(" ");
		}
		sb.append(this.m_Creator);
		sb.append(" " + this.m_Type);
		sb.append(" " + this.m_LastModifiedStringFormat.format(new Date(this.m_LastModified)));
		return sb.toString();
	}

	public boolean isDirty() {
		return this.m_Touched;
	}

	public void setDirty(boolean flag) {
		this.m_Touched = flag;
	}

	public String getCreator() {
		return m_Creator;
	}

	public Date getCreated() {
		return m_Created;
	}

	public String getLastModifier() {
		return m_LastModifier;
	}

	public Date getLastModified() {
		return new Date(m_LastModified);
	}

	public boolean isFromSource() {
		return (this.m_Iteration == 0);
	}

	public Type getType() {
		return m_Type;
	}

	public boolean isCyclic() {
		return m_IsCyclic;
	}

	public boolean isDirected() {
		return m_IsDirected;
	}

	public boolean isGraph() {
		return m_IsTree;
	}

	public boolean isOrdered() {
		return m_IsOrdered;
	}

	public boolean isFinite() {
		return m_IsFinite;
	}

	public boolean isMulitGraph() {
		return m_IsMultiGraph;
	}

	public String getAbsolutePath(int i) {
		return this.m_FileNames.get(i);
	}

	public String getFileName(int i) {
		String s = this.m_FileNames.get(i);
		if (s.contains(Constants.getFileSep())) {
			String fileSep = Constants.getFileSep();
			String[] names = s.split(fileSep);
			s = "";
			for (String k : names) {
				s += k.substring(k.lastIndexOf(File.separator) + 1) + fileSep;
			}
			s = s.substring(0, s.length() - 2);
		} else {
			s = s.trim();
			s = s.substring(s.lastIndexOf(File.separator) + 1);
		}
		return s;
	}

	public int getNumberOfFiles() {
		return this.m_FileNames.size();
	}

	private void init() {
		this.m_Touched = false;
		this.m_Iteration = 0;
		this.m_LastModifier = this.m_Creator;
		this.m_Created = new Date();
		this.m_LastModified = System.currentTimeMillis();
		this.m_Size = 0;
		this.m_LastModifiedStringFormat = new SimpleDateFormat("dd.MM hh:mm:ss");
		setAttributes();
	}

	private void setAttributes() {
		switch (m_Type) {
		case AST:
			m_IsCyclic = false;
			m_IsDirected = true;
			m_IsTree = true;
			m_IsOrdered = true;
			m_IsMultiGraph = false;
			m_IsFinite = true;
			break;
		case CST:
			m_IsCyclic = false;
			m_IsDirected = true;
			m_IsTree = true;
			m_IsOrdered = true;
			m_IsMultiGraph = false;
			m_IsFinite = true;
			break;
		case DFG:
			m_IsCyclic = false;
			m_IsDirected = true;
			m_IsTree = true;
			m_IsOrdered = false;
			m_IsMultiGraph = false;
			m_IsFinite = true;
			break;
		case CFG:
			m_IsCyclic = true;
			m_IsDirected = true;
			m_IsTree = false;
			m_IsOrdered = false;
			m_IsMultiGraph = false;
			m_IsFinite = true;
			break;
		case OTHER:
			m_IsCyclic = true;
			m_IsDirected = true;
			m_IsTree = false;
			m_IsOrdered = false;
			m_IsMultiGraph = true;
			m_IsFinite = false;
			break;
		default:
			throw new UnsupportedOperationException("Graphtype " + m_Type + " not implemented yet");
		}
	}

	public int getSize() {
		return this.m_Size;
	}

	public void setSize(int size) {
		this.m_Size = size;
	}

	public List<String> getFileNames() {
		return this.m_FileNames;
	}

}
