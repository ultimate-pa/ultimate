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
package de.uni_freiburg.informatik.ultimate.lib.pea;

public class Transition {
    Phase src, dest;
    CDD guard;
    String[] resets;

    /**
     * @return Returns the guard.
     */
    public CDD getGuard() {
        return guard;
    }
    /**
     * @param guard The guard to set.
     */
    public void setGuard(CDD guard) {
        this.guard = guard;
    }
    public Transition(Phase src, CDD guard, String[] resets, Phase dest) {

	this.src = src;
	this.guard = guard;
	this.resets = resets;
	this.dest = dest;
    }

    @Override
	public String toString() {
	String destName = dest.toString();
	if (destName.length() < 33) {
		destName = (destName + "                                 ")
		.substring(0, 33);
	}
	final StringBuffer result = new StringBuffer(" -> ").append(destName)
	    .append(" guard ").append(guard);

	if (resets.length > 0) {
	    result.append(" resets {");
	    String comma = "";
	    for (int i = 0; i < resets.length; i++) {
		result.append(comma).append(resets[i]);
		comma = ",";
	    }
	    result.append("}");
	}
	return result.toString();
    }

    /**
     * @return Returns the dest.
     */
    public Phase getDest() {
        return dest;
    }
    /**
     * @return Returns the resets.
     */
    public String[] getResets() {
        return resets;
    }
    /**
     * @return Returns the src.
     */
    public Phase getSrc() {
        return src;
    }
    
    //F�r den Fall dass ein Guard eine ODER Verkn�pfung hat werden die Transitionen manchmal nicht korrekt 
    //vereinfacht; Bsp: ein Guard der Form "\neg P || c<10 " auf einer Transition mit dest.StateInvariant = P 
    //sollte auf "c<10" vereinfacht werden
    public void simplifyGuard(){
    	final CDD[] guardDNF= guard.toDNF();
    	final int length = guardDNF.length;
    	if (length >=1) //for 1: although no "OR" is used in the guard, we need to prime it again
    	{	
    		//check for every conjunctive clause whether s(p)&guard is satisfiable
    		//if s(p)&guard is not satisfiable, we do not need that conjunct!
    		//and build up the CDD again
    		//If s(p)&guard is not satisfiable for any guardpart, then we can delete this edge
    		CDD simplifiedGuard = CDD.FALSE;
    		final CDD[] simplifiedGuardDNF = new CDD[length];
    		int j=0;
    		for (int i=0; i< length; i++){
    			CDD guardPart = guardDNF[i];
    			final CDD guardPartUnprimed = guardPart.unprime();
    			
    			if (dest.getStateInvariant().and(guardPartUnprimed)!=CDD.FALSE){
    				final String guardPartString = guardPart.toString();
    				if (guardPartString.matches(guardPartUnprimed.toString())){
    					//Spezialfall f�r clockinvariante!
    					if (!(guardPartString.contains("<") ||
    							guardPartString.contains(">")||
    							guardPartString.contains("\u2264")|| 
    							guardPartString.contains("\u2265"))){
    					guardPart = guardPart.prime();
    				}}
    				
    				simplifiedGuardDNF[j]=guardPart;
    				simplifiedGuard=simplifiedGuard.or(guardPart);
    				j++;
    			}
    		}
    		setGuard(simplifiedGuard); 		 		
    		
    	}
    	
    }
}
