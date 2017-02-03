/*
 *
 * This file is part of the PEA tool set
 * 
 * The PEA tool set is a collection of tools for 
 * Phase Event Automata (PEA). See
 * http://csd.informatik.uni-oldenburg.de/projects/peatools.html
 * for more information.
 * 
 * Copyright (C) 2005-2006, Department for Computing Science,
 *                          University of Oldenburg
 * 
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License
 * as published by the Free Software Foundation; either version 2
 * of the License, or (at your option) any later version.
 * 
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 * 
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301, USA
 */
package de.uni_freiburg.informatik.ultimate.lib.pea.modelchecking;

import de.uni_freiburg.informatik.ultimate.lib.pea.CDD;
import de.uni_freiburg.informatik.ultimate.lib.pea.CounterTrace;


/**
 *
 *A model checkable trace is represented as a <code>CounterTrace</code>-Object
 *with entry and exit sync event, missing events following the last phase,
 *and a specification whether the trace is negated, represented as <code>false</code> 
 *or not negated.
 *
 *@see de.uni_freiburg.informatik.ultimate.lib.pea.CounterTrace
 *@see de.uni_freiburg.informatik.ultimate.lib.pea.CDD
 *
 *@author Roland Meyer
 *
 */
public class MCTrace {
	
	private CounterTrace trace = null;
	private CDD entrySync = null;
	private CDD exitSync = null;
	private CDD missingEvents = null;
	private boolean spec = true;
	
	public MCTrace(CounterTrace trace, CDD entry, CDD exit, CDD missing, boolean spec){
		this.trace = trace;
		entrySync = entry;
		exitSync = exit;
		missingEvents = missing;
		this.spec = spec;
	}
	
	public MCTrace(){
	}
	
	/**
	 * @param entrySync The entrySync to set.
	 */
	public void setEntrySync(CDD entrySync) {
		this.entrySync = entrySync;
	}
    
	/**
	 * @param exitSync The exitSync to set.
	 */
	public void setExitSync(CDD exitSync) {
		this.exitSync = exitSync;
	}
    
	/**
	 * @param missingEvents The missingEvents to set.
	 */
	public void setMissingEvents(CDD missingEvents) {
		this.missingEvents = missingEvents;
	}
    
	/**
	 * @param spec The spec to set.
	 */
	public void setSpec(boolean spec) {
		this.spec = spec;
	}
    
	/**
	 * @param trace The trace to set.
	 */
	public void setTrace(CounterTrace trace) {
		this.trace = trace;
	}
	
	/**
	 * @return Returns the trace.
	 */
	public CounterTrace getTrace() {
		return trace;
	}
    
    /**
     * @return Returns the entrySync.
     */
    public CDD getEntrySync() {
        return entrySync;
    }
    
    /**
     * @return Returns the exitSync.
     */
    public CDD getExitSync() {
        return exitSync;
    }
    
    /**
     * @return Returns the missingEvents.
     */
    public CDD getMissingEvents() {
        return missingEvents;
    }
    
    /**
     * @return Returns the spec flag.
     */
    public boolean getSpec() {
        return spec;
    }
}
