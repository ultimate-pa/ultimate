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
package de.uni_freiburg.informatik.ultimate.core.model.models;

import java.io.File;
import java.io.Serializable;
import java.text.DateFormat;
import java.text.SimpleDateFormat;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Date;
import java.util.List;

/**
 * Intended for separating different types of graphs and trees like Call Graphs, Data Flow Graphs, AST Should also
 * specify their special attributes
 *
 * Change in Ultimate 2.0:
 *
 * A GraphType should be identified by its String representation. Unlike object identity this should be preserved during
 * serialization. Therefore the equals method now checks for equal String representation instead of object identity. In
 * order to be consistent this change is carried to hashCode.
 *
 * The changes will allow the GraphType to remain a suitable key in the model managers in-memory map and its string
 * representation to be the key in the repository.
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 */
public class ModelType implements Serializable {

	private static final long serialVersionUID = -2922069733243189149L;

	private int mSize;

	private final String mCreator;
	private Date mCreated;
	private long mLastModified;
	private String mLastModifier;
	private final Type mType;
	private int mIteration;
	private boolean mTouched;
	private final List<String> mFileNames;
	private DateFormat mLastModifiedStringFormat;

	private boolean mIsCyclic;
	private boolean mIsDirected;
	private boolean mIsTree;
	private boolean mIsOrdered;
	private boolean mIsMultiGraph;
	private boolean mIsFinite;

	/**
	 * @author dietsch
	 */
	public enum Type {
		AST, CG, CFG, DFG, CST, TS, PG, OTHER, CORRECTNESS_WITNESS, VIOLATION_WITNESS
	}

	public ModelType(final String creatorPluginID, final Type type, final Collection<String> fileNames) {
		if (fileNames == null) {
			throw new IllegalArgumentException("A graphtype has to have at least one filename");
		}
		if (type == null) {
			throw new IllegalArgumentException("A graphtype has to have a type");
		}
		mCreator = creatorPluginID;
		mType = type;
		mFileNames = new ArrayList<>(fileNames);

		init();
	}

	/**
	 * Should be set AFTER a write operation was performed on this data structure was completed
	 *
	 * @param modifierPluginID
	 *            The ID of the plugin which performed the write operation
	 */
	public void modified(final String modifierPluginID) {
		setDirty(true);
		mLastModifier = modifierPluginID;
		mLastModified = System.currentTimeMillis();
		mIteration++;
	}

	/*
	 * (non-Javadoc)
	 *
	 * @see java.lang.Object#equals(java.lang.Object)
	 */
	@Override
	public boolean equals(final Object obj) {
		if (obj instanceof ModelType) {
			final ModelType t = (ModelType) obj;
			return t.mLastModified == mLastModified && t.mCreator.equals(mCreator);
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
		return (int) mLastModified;
	}

	/*
	 * (non-Javadoc)
	 *
	 * @see java.lang.Object#toString()
	 */
	@Override
	public String toString() {
		final StringBuffer sb = new StringBuffer();
		for (final String fileName : mFileNames) {
			sb.append(new File(fileName).getName());
		}
		if (sb.length() > 0) {
			sb.append(" ");
		}
		sb.append(mCreator);
		sb.append(" " + mType);
		sb.append(" " + mLastModifiedStringFormat.format(new Date(mLastModified)));
		return sb.toString();
	}

	public boolean isDirty() {
		return mTouched;
	}

	public void setDirty(final boolean flag) {
		mTouched = flag;
	}

	public String getCreator() {
		return mCreator;
	}

	public Date getCreated() {
		return mCreated;
	}

	public String getLastModifier() {
		return mLastModifier;
	}

	public Date getLastModified() {
		return new Date(mLastModified);
	}

	public boolean isFromSource() {
		return mIteration == 0;
	}

	public Type getType() {
		return mType;
	}

	public boolean isCyclic() {
		return mIsCyclic;
	}

	public boolean isDirected() {
		return mIsDirected;
	}

	public boolean isGraph() {
		return mIsTree;
	}

	public boolean isOrdered() {
		return mIsOrdered;
	}

	public boolean isFinite() {
		return mIsFinite;
	}

	public boolean isMulitGraph() {
		return mIsMultiGraph;
	}

	public String getAbsolutePath(final int i) {
		return mFileNames.get(i);
	}

	public String getFileName(final int i) {
		String s = mFileNames.get(i);
		if (s.contains(", ")) {
			final String fileSep = ", ";
			final String[] names = s.split(fileSep);
			s = "";
			for (final String k : names) {
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
		return mFileNames.size();
	}

	private void init() {
		mTouched = false;
		mIteration = 0;
		mLastModifier = mCreator;
		mCreated = new Date();
		mLastModified = System.currentTimeMillis();
		mSize = 0;
		mLastModifiedStringFormat = new SimpleDateFormat("dd.MM hh:mm:ss");
		setAttributes();
	}

	private void setAttributes() {
		switch (mType) {
		case AST:
			mIsCyclic = false;
			mIsDirected = true;
			mIsTree = true;
			mIsOrdered = true;
			mIsMultiGraph = false;
			mIsFinite = true;
			break;
		case CST:
			mIsCyclic = false;
			mIsDirected = true;
			mIsTree = true;
			mIsOrdered = true;
			mIsMultiGraph = false;
			mIsFinite = true;
			break;
		case DFG:
			mIsCyclic = false;
			mIsDirected = true;
			mIsTree = true;
			mIsOrdered = false;
			mIsMultiGraph = false;
			mIsFinite = true;
			break;
		case CFG:
			mIsCyclic = true;
			mIsDirected = true;
			mIsTree = false;
			mIsOrdered = false;
			mIsMultiGraph = false;
			mIsFinite = true;
			break;
		case OTHER:
			mIsCyclic = true;
			mIsDirected = true;
			mIsTree = false;
			mIsOrdered = false;
			mIsMultiGraph = true;
			mIsFinite = false;
			break;
		default:
			// do nothing
			break;
		}
	}

	public int getSize() {
		return mSize;
	}

	public void setSize(final int size) {
		mSize = size;
	}

	public List<String> getFileNames() {
		return mFileNames;
	}

}
