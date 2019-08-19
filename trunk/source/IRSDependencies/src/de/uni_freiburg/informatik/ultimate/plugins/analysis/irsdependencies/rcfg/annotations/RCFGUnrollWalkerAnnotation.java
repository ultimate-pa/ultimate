/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE IRSDependencies plug-in.
 * 
 * The ULTIMATE IRSDependencies plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE IRSDependencies plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE IRSDependencies plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE IRSDependencies plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE IRSDependencies plug-in grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.analysis.irsdependencies.rcfg.annotations;


import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;

public class RCFGUnrollWalkerAnnotation extends IRSDependenciesAnnotation {

	private static final long serialVersionUID = 1L;
	private final String[] mAttribFields = { "IsLoopEntry", "IsLoopExit",
			"Honda", "IsChecked" };
	
	private boolean mIsLoopEntry;
	private boolean mIsLoopExit;
	private IcfgLocation mHonda;

	public RCFGUnrollWalkerAnnotation(IcfgLocation honda, boolean isEntry,
			boolean isExit) {
		setLoopEntry(isEntry);
		setIsLoopExit(isExit);
		setHonda(honda);
	}
	
	
	@Override
	protected String[] getFieldNames() {
		return mAttribFields;
	}
	
	@Override
	protected Object getFieldValue(String field) {
		switch (field) {
		case "IsLoopEntry":
			return isLoopEntry();
		case "IsLoopExit":
			return isLoopExit();
		case "Honda":
			return getHonda();
		default:
			return null;
		}
	}


	public IcfgLocation getHonda() {
		return mHonda;
	}


	public void setHonda(IcfgLocation mHonda) {
		this.mHonda = mHonda;
	}


	public boolean isLoopExit() {
		return mIsLoopExit;
	}


	public void setIsLoopExit(boolean mIsLoopExit) {
		this.mIsLoopExit = mIsLoopExit;
	}


	public boolean isLoopEntry() {
		return mIsLoopEntry;
	}


	public void setLoopEntry(boolean mIsLoopEntry) {
		this.mIsLoopEntry = mIsLoopEntry;
	}



}
