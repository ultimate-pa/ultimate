/* $Id: PEA2TCSJ2XMLConverter.java 326 2008-08-01 16:41:13Z jfaber $ 
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
package pea.modelchecking;

import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Iterator;
import java.util.List;
import org.apache.log4j.Logger;


import pea.Phase;
import pea.PhaseEventAutomata;
import pea.Transition;

public class PEA2TCSJ2XMLConverter {

	protected static final String STATE_NAME = "state";

	protected static final String DEFAULT_LOGGER = "PEA2TCSJ2XMLConverter";

    protected Logger logger = null;

    protected TCSFormulaJ2XMLConverter formulaConverter = null;

	protected FileWriter writer;

    protected List<String> events = null;
    protected List<String> clocks = null;
    protected List<String> variables = null;
    
	protected ArrayList[] additionalVariables = null;
	protected ArrayList[] additionalTypes = null;
    
	protected boolean rename = false;
	
	protected int peaCounter = 0;
	
    /**
     * Initialises the PEA2TCSJ2XMLConverter object. Takes as parameter a string
     * that defines the loggername for the built in log4j logger. If the string
     * is empty, the default name <code>PEA2TCSJ2XMLConverter</code> is used. An
     * application using a PEA2TCSJ2XMLConverter object has to make sure that the
     * logger is initialised via <code>PropertyConfigurator.configure()</code>.
     * 
     * @param loggerName
     * @see Logger
     * @see PropertyConfigurator
     */
    public PEA2TCSJ2XMLConverter(String loggerName) throws Exception {
        if (loggerName.equals("")) {
            this.logger = Logger.getLogger(PEAJ2XMLConverter.DEFAULT_LOGGER);
        } else {
            this.logger = Logger.getLogger(loggerName);
        }

        this.formulaConverter = new TCSFormulaJ2XMLConverter();

        this.clocks = new ArrayList<String>();
        this.events = new ArrayList<String>();
        this.variables = new ArrayList<String>();
    }

    /**
     * Initialises the PEA2TCSJ2XMLConverter object with the default logger.
     */
    public PEA2TCSJ2XMLConverter() throws Exception {
        this("");
    }
	
	
	public void convert(PhaseEventAutomata[] peas, String file, boolean rename) {
		try {
			this.rename = rename;
			//peas[0].dump();
			peaCounter = 0;
			this.writer = new FileWriter(file);
			if (peas.length == 0) {
				throw new RuntimeException(
						"The array of peas is not allowed to be empty");
			}

			this.writer
					.write("<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n"+
						"<tcsn xmlns:xalan=\"http://xml.apache.org/xalan\">\n");
			
			for (int i = 0; i < peas.length; i++) {
				this.logger.info("Trying to create tcsNode " + i);
				this.createPhaseEventAutomaton(peas[i]);
				this.logger.info("Creating tcsNode " + i + " successful");
				peaCounter++;
			}

			this.writer.write("</tcsn>\n");

			this.writer.flush();
			this.writer.close();
		} catch (Exception e) {
			System.out.println("Errors writing the TCS-XML representation of pea");
			e.printStackTrace();
		}
	}

	protected void createPhaseEventAutomaton(PhaseEventAutomata pea) throws IOException{
		if (pea.getPhases().length == 0) {
			throw new RuntimeException(
					"PEA with phase count = 0 is not allowed");
		}
		if (pea.getInit().length == 0) {
			throw new RuntimeException(
					"PEA with initial phase count = 0 is not allowed");
		}

		this.clocks.clear();
		this.events.clear();
		this.variables.clear();

        // Write variable lists
        writer.write("  <variables>\n");
        writer.write("    <variable name=\"disc\" type=\"bool\"/>\n");
        writer.write("    <variable name=\"len\" type=\"time\"/>\n");

        if(this.additionalVariables != null
                 && !this.additionalVariables[peaCounter].isEmpty()){
            Iterator addVarIterator = this.additionalVariables[peaCounter].iterator();
            Iterator typesIterator = this.additionalTypes[peaCounter].iterator();
            while (addVarIterator.hasNext()) {
                String actVariable = (String) addVarIterator.next();
                String typeName = (String) typesIterator.next();
                writer.write("    <variable name=\"" + actVariable
                        + "\" type=\"" + typeName + "\"/>\n");
            }
        }
        writer.write("  </variables>\n");

        
		writer.write("<tcs name=\"" + pea.getName() + "\">\n");

     
		// Create phase nodes
		writer.write("<locations>\n");
		
		//TODO: THIS SHOULD NOT BE DONE THIS WAY
		//No need to fill variables and events lists
		//this.initMaps(pea.getPhases());
		
		Phase[] phases = pea.getPhases();
		if(this.rename){
			int stateCounter = 0;
			for(int i=0; i<phases.length; i++){
				if(!phases[i].getName().equals(SimplifyPEAs.BADSTATESTRING))
                	phases[i].setName(PEA2TCSJ2XMLConverter.STATE_NAME+stateCounter);    
				stateCounter++;
			}
		}
		Phase[] init = pea.getInit();
		List<Phase> temp = Arrays.asList(phases);
		temp.removeAll(Arrays.asList(init));
		Phase[] notInitPhases = (Phase[])temp.toArray(new Phase[0]);

		for (int i = 0; i < init.length; i++) {
			this.createPhaseNode(init[i], true);
		}
		for (int i = 0; i < notInitPhases.length; i++) {
			this.createPhaseNode(notInitPhases[i], false);
		}
		writer.write("</locations>\n");

		// Create transition nodes
		if (this.peaHasTransitions(pea)) {
			writer.write("<transitions>\n");
			for (int i = 0; i < phases.length; i++) {
				List transitions = phases[i].getTransitions();
				Iterator transIter = transitions.iterator();
				while (transIter.hasNext()) {
					Transition trans = (Transition) transIter.next();
					this.createTransitionNode(trans);
					
				}
			}
			writer.write("</transitions>\n");
		}

		// Add additional variables to var list.
//		if (!this.variables.isEmpty() || 
//				(this.additionalVariables != null
//				 && !this.additionalVariables[peaCounter].isEmpty())) {
//			writer.write("  <variables>\n");
//			if(this.additionalVariables != null
//					 && !this.additionalVariables[peaCounter].isEmpty()){
//				Iterator addVarIterator = this.additionalVariables[peaCounter].iterator();
//				Iterator typesIterator = this.additionalTypes[peaCounter].iterator();
//				while (addVarIterator.hasNext()) {
//					String actVariable = (String) addVarIterator.next();
//					String typeName = (String) typesIterator.next();
//					writer.write("    <variable name=\"" + actVariable
//							+ "\" type=\"" + typeName + "\"/>\n");
//				}
//			}
//			if (!this.variables.isEmpty()) {
//				Iterator variablesIterator = this.variables.iterator();
//				while (variablesIterator.hasNext()) {
//					String actVariable = (String) variablesIterator.next();
//					writer.write("    <variable name=\"" + actVariable
//							+ "\" type=\"default_type\"/>\n");
//				}
//			}
//			writer.write("  </variables>\n");
//		}

		writer.write("</tcs>\n");

	}

	private boolean peaHasTransitions(PhaseEventAutomata pea) {
		Phase[] phases = pea.getPhases();
		for (int i = 0; i < phases.length; i++) {
			if (phases[i].getTransitions().size() > 0) {
				return true;
			}
		}
		return false;
	}

	protected void createPhaseNode(Phase phase, boolean init) throws IOException {
		this.writer.write("<location name=\"" + phase.getName() + "\" initial=\""
				+ init + "\">\n");
		this.writer.write("<init-constraint>");
		if(init==true){
			/*if(phase.getStateInvariant()==CDD.TRUE){
				this.writer.write("\n StateInvariant true\n");
			}
			if(phase.getClockInvariant()==CDD.TRUE){
				this.writer.write("\n ClockInvariant true\n");
			}*/
			StringBuffer initConstraintString = new StringBuffer("! disc /\\ len &gt; 0 ");
			String[] stateInvDis = this.formulaConverter.getDisjuncts(false, phase.getStateInvariant(), new ArrayList<String>(), new ArrayList<String>());
			String[] clockInvDis = this.formulaConverter.getDisjuncts(false, phase.getClockInvariant(), new ArrayList<String>(), new ArrayList<String>());
			if (!this.clocks.isEmpty()) {
				Iterator clocksIterator = this.clocks.iterator();
				while (clocksIterator.hasNext()) {
					String actClock = (String) clocksIterator.next();
					initConstraintString.append(" /\\ "+actClock+" = 0 ");
				}
			}
			for(int i=0; i<stateInvDis.length;i++){
				for(int j=0; j<clockInvDis.length; j++){
					if(i!=0||j!=0){
						this.writer.write("\\/");
					}
					this.writer.write(initConstraintString.toString());
					if(!stateInvDis[i].equals("")){
						this.writer.write(" /\\ "+stateInvDis[i]); 
					}
					if(!clockInvDis[j].equals("")){
						this.writer.write(" /\\ "+clockInvDis[j]);
					}
				}
			}
		}else{
			this.writer.write("false");
		}
		this.writer.write("</init-constraint>");
		this.writer.write("</location>\n");
	}

	protected void createTransitionNode(Transition trans)throws IOException {
		String source = trans.getSrc().getName();
		String dest = trans.getDest().getName();
		boolean sourceEqualDest = source.equals(dest);
        this.logger.info("Creating transition from " + source + " to " + dest);
		
        //////////////////////////////////////////////////////////////
        //////////////////////////////////////////////////////////////
        ////////COMPUTE CONT//////////////////////////////////////////
        //////////////////////////////////////////////////////////////
        //////////////////////////////////////////////////////////////
        StringBuffer cont = new StringBuffer("");
        if(sourceEqualDest){
        	cont.append("! disc /\\ disc' ");
        	if (!this.clocks.isEmpty()) {
				Iterator clocksIterator = this.clocks.iterator();
				while (clocksIterator.hasNext()) {
					String actClock = (String) clocksIterator.next();
					cont.append(" /\\ "+actClock+"' = "+actClock+" + len ");
				}
			}
        	for(int i=0; i<this.additionalVariables.length;i++) {
				Iterator varIterator = this.additionalVariables[i].iterator();
				while (varIterator.hasNext()) {
					String actVariable = (String) varIterator.next();
					cont.append(" /\\ "+actVariable+"' = "+actVariable);
				}
				
			}
        	if (!this.events.isEmpty()) {
				Iterator eventIterator = this.events.iterator();
				while (eventIterator.hasNext()) {
					String actEvent = (String) eventIterator.next();
					cont.append(" /\\ "+actEvent+"' = "+actEvent);
				}
			}
        }
        
        //////////////////////////////////////////////////////////////
        //////////////////////////////////////////////////////////////
        ////////COMPUTE CONT FINISHED/////////////////////////////////
        //////////////////////////////////////////////////////////////
        //////////////////////////////////////////////////////////////
    
        //////////////////////////////////////////////////////////////
        //////////////////////////////////////////////////////////////
        ////////COMPUTE DISC//////////////////////////////////////////
        //////////////////////////////////////////////////////////////
        //////////////////////////////////////////////////////////////
        String[] guardDis = this.formulaConverter.getDisjuncts(false, trans.getGuard(), this.clocks, this.events);    
		StringBuffer discConst = new StringBuffer("disc /\\ ! disc'");
		String[] resets = trans.getResets();
		List<String> notReset = new ArrayList<String>(this.clocks);
		notReset.removeAll(Arrays.asList(resets));
		
		for(int i=0; i<resets.length; i++) {
			discConst.append(" /\\ "+resets[i]+"' = 0");
		}
		Iterator notResetIter = notReset.iterator();
		while (notResetIter.hasNext()) {
			String aktNotReset = (String) notResetIter.next();
			discConst.append(" /\\ "+aktNotReset+"' = "+aktNotReset);
		}
		
		for(int i=0; i<guardDis.length;i++){
			guardDis[i]+="/\\ "+discConst.toString().trim();
		}
		//////////////////////////////////////////////////////////////
        //////////////////////////////////////////////////////////////
        ////////COMPUTE DISC FINISHED/////////////////////////////////
        //////////////////////////////////////////////////////////////
        //////////////////////////////////////////////////////////////
        
		//////////////////////////////////////////////////////////////
        //////////////////////////////////////////////////////////////
        ////////COMPUTE INVp2/////////////////////////////////////////
        //////////////////////////////////////////////////////////////
        //////////////////////////////////////////////////////////////
		String[] stateInvDis = this.formulaConverter.getDisjuncts(true,trans.getDest().getStateInvariant(), new ArrayList<String>(), new ArrayList<String>());
		String[] clockInvDis = this.formulaConverter.getDisjuncts(true, trans.getDest().getClockInvariant(), new ArrayList<String>(), new ArrayList<String>());
		String[] invp2 = new String[stateInvDis.length*clockInvDis.length];
		for(int i=0; i<stateInvDis.length; i++){
			for(int j=0; j<clockInvDis.length; j++){
				/*if(trans.getDest().getStateInvariant()==CDD.TRUE){
					this.writer.write("\n Stateinvariant is true\n");
				}
				if(trans.getDest().getClockInvariant()==CDD.TRUE){
					this.writer.write("\n Clockinvariant is true\n");		
				}*/
				invp2[(i*clockInvDis.length)+j] = "len' &gt; 0"; 
				if(!stateInvDis[i].equals("")){
					invp2[(i*clockInvDis.length)+j] += " /\\ "+stateInvDis[i]; 
				}
				if(!clockInvDis[j].equals("")){
					invp2[(i*clockInvDis.length)+j] += " /\\ "+clockInvDis[j];
				}
			}
		}
		//////////////////////////////////////////////////////////////
        //////////////////////////////////////////////////////////////
        ////////COMPUTE INVp2 FINISHED////////////////////////////////
        //////////////////////////////////////////////////////////////
        //////////////////////////////////////////////////////////////
        
		//this.writer.write("<transition src = \""+source+"\" dest = \""+dest+"\">");
		for(int i=0; i<invp2.length; i++){
			for(int j=0; j<guardDis.length; j++){
				/*if(i!=0 || j!=0){
					this.writer.write(" \\/ ");
				}*/
				this.writer.write("<transition src = \""+source+"\" dest = \""+dest+"\">");
				this.writer.write(invp2[i]+" /\\ "+guardDis[j]);
				this.writer.write("</transition>\n");
				
			}
			if(sourceEqualDest){
				this.writer.write("<transition src = \""+source+"\" dest = \""+dest+"\">");
				//this.writer.write("\\/" + invp2[i] +" /\\ "+cont.toString());
				this.writer.write(invp2[i] +" /\\ "+cont.toString());
				this.writer.write("</transition>\n");
			}
		}
		//this.writer.write("</transition>\n");
	}

	/**
	 * @param additionalVariables Sets the list of additional variables that has to be
	 * inserted to the output-document.
	 */
	public void setAdditionalVariables(ArrayList[] additionalVariables) {
		this.additionalVariables = additionalVariables;
	}
		
	/**
	 * @param types Sets the types belonging to additionalVariables.
	 */
	public void setAdditionalTypes(ArrayList[] types) {
		this.additionalTypes = types;
	}
	

        /**
	 * @param args
	 */
	public static void main(String[] args) {
		try{
			PEAXML2JConverter xml2j = new PEAXML2JConverter(false);
			PhaseEventAutomata[] peas = xml2j.convert("./pea/modelchecking/CaseStudy/ComNW.xml");
			PEA2TCSJ2XMLConverter pea2tcsFast = new PEA2TCSJ2XMLConverter();
			pea2tcsFast.convert(peas, "./pea/modelchecking/example/tcs.xml", false);
		}catch(Exception e){
			System.out.println("Outermost exception");
			e.printStackTrace();
		}

	}

}
