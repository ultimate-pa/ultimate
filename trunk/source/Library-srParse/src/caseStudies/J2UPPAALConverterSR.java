package caseStudies;


import java.io.BufferedWriter;
import java.io.FileWriter;
import java.io.IOException;
import java.util.List;
import java.util.Vector;


import pea.CDD;
import pea.Phase;
import pea.Transition;
import pea.PhaseEventAutomata;
import pea.modelchecking.J2UPPAALConverter;
//import pea.modelchecking.J2UPPAALConverter.XMLString;


public class J2UPPAALConverterSR extends J2UPPAALConverter {
	
	private Vector<SimpleDlFind.FoundEntry> suspects;
	//private Vector<Transition> susp_trans;
	private Phase suspect;
	private Phase suspect2;
	//private boolean susp_reach;
	
	protected void addPEAStates(Phase[] phases) throws IOException {
		super.addPEAStates(phases);
		
		//if( suspects.size()>0 ) 
		{
   		 writer.write("<location id = \"dlsusp\""+">\n"+
   	                "  <name>dlsusp</name>\n");
   	        writer.write("</location>\n");
   	        
   	     writer.write("<location id = \"dlsusp2\""+">\n"+
            "  <name>dlsusp2</name>\n");
    writer.write("</location>\n");
        }
	}
	
	protected void addPEATransitions(Phase[] phases) {
		//super.addPEATransitions(phases);
		suspect=new Phase("dlsusp");
		suspect2=new Phase("dlsusp2");
		
		Vector<Transition> transitions = new Vector<Transition>();  
		
		Transition tr=new Transition(suspect, CDD.TRUE, new String[0],suspect2);
		transitions.add(tr);
	   	 
    	for(int i=0; i<phases.length; i++) {
    		Phase phase = phases[i];
    		transitions.addAll(phase.getTransitions());
    		if( phase.isDlSuspect )
    		{
    			CDD guard= phase.getClockInvariant().negate();
    			for( int j=0;j<phase.getTransitions().size();j++ )
    				guard=guard.and( phase.getTransitions().get(j).getGuard().negate() );
    			
    			//if( guard!=CDD.FALSE )
    				//susp_reach=true;
    			Transition t=new Transition(phase,guard, new String[0], suspect);
    			transitions.add(t);
    			
    		}
       }    
   	 
    	this.transCount = transitions.size();
    	for (int j=0; j<transCount; j++){
    		
    		Transition trans = transitions.elementAt(j);
    		this.createPEATransitionString(trans);
    	}
	}
	
	protected void createPEATransitionString(Transition transition){
        String[] disjuncts = this.getDisjuncts(transition.getGuard());        
        String[] resets = transition.getResets();
        StringBuffer assignment = new StringBuffer();
        
        for (int i = 0; i < resets.length; i++) {
            assignment.append(resets[i]).append(":=0, ");
        }
        assignment.append("timer:=0");
        
        for(int i=0; i<disjuncts.length; i++) {
        	
        	String source = transition.getSrc().getName();
        	String destination = transition.getDest().getName();
        	
        	if(source.matches(destination)&& (resets.length<=0)){
        		//selfloops in which no clock is reset do not need to be transfered to the uppaal model
        		this.deletedSelfloops++; //only for measurement
        	}
        	else
        	{
        		//if s(p)&s(p')&g is unsatisfiable, delete this edge
        		//CDD sourceInv = transition.getSrc().getStateInvariant();
        		CDD destInv = transition.getDest().getStateInvariant();
        		CDD guard = transition.getGuard();        		
        		if (guard.and(destInv)==CDD.FALSE){
        			//do nothing
        			this.deletedTransitions++;
        		}
        		else{
        	
        	try {
				writer.write("<transition>\n"+
				"  <source ref = \""+source+"\"/>\n"+
				"  <target ref = \""+destination+"\"/>\n");
				
				if( source.compareTo( suspect.getName() )==0 )
					writer.write( "<label kind='synchronisation'>dlock!</label> " );
				else
					if( destination.compareTo( suspect.getName() )==0 )
						{
						 if (disjuncts[i].isEmpty()){
				            	writer.write("  <label kind = \"guard\"> timer "+XMLString.GREATER+" 0 </label>\n");
				            }
				            else 
				            {
				            	disjuncts[i]=disjuncts[i].replaceAll( "&gt; ", "&gt;= " );
				            	disjuncts[i]=disjuncts[i].replaceAll( "&lt; ", "&lt;= " );
				            	writer.write("  <label kind = \"guard\">"+disjuncts[i]+ XMLString.AND+"timer"+XMLString.GREATER+"0 </label>\n"); 
				            }            
				            writer.write("  <label kind = \"assignment\">"+assignment.toString()+"</label>\n");
				            
						}
					else
						{
						 if (disjuncts[i].isEmpty()){
				            	writer.write("  <label kind = \"guard\"> timer "+XMLString.GREATER+" 0 </label>\n");
				            }
				            else 
				            {
				            	writer.write("  <label kind = \"guard\">"+disjuncts[i]+ XMLString.AND+"timer"+XMLString.GREATER+"0 </label>\n"); 
				            }            
				            writer.write("  <label kind = \"assignment\">"+assignment.toString()+"</label>\n");
				            
						}
				
				writer.write("</transition>\n");
		            
		            writer.flush();
			} catch (IOException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}   
        }}
        }
    }
	
	
	public void writePEA2UppaalFile(String file, PhaseEventAutomata pea/*, Vector<SimpleDlFind.FoundEntry> suspects*/) {    	
		//susp_trans=new Vector<Transition>();
		//this.suspects=suspects;
		//susp_reach=false;
    	long actTime = System.currentTimeMillis();
        try {
	        this.writer =	new BufferedWriter(new FileWriter(file));
	        
	        //FileWriter writer = new FileWriter(file);
	        String clockDeclaration = addDeclarationOfClocks(pea);
	        
	        //First we need to simplify some guards
	        pea.simplifyGuards();
	        
	        //Uppaal does not accept system names that are too long --< we use only a short version of the name
	        int namelength = pea.getName().length();
	        String shortName = pea.getName();
	        if (namelength >= 31){
	        	shortName = pea.getName().substring(0,31);
	        }
	          	
	        
	        System.out.println(shortName);
	        
	        
	        writer.write("<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n" +
	                     "<!DOCTYPE nta PUBLIC \"-//Uppaal Team//DTD Flat System 1.0//EN\" \"http://www.docs.uu.se/docs/rtmv/uppaal/xml/flat-1_0.dtd\"> \n" +
	                     "<nta>\n"+
	                     "<declaration/>\n" +
	                     "<template>\n" +
	                     "<name>"+shortName+"</name>\n"+
	                     "<parameter>urgent chan &amp;dlock</parameter>"+
	                     "<declaration>"+clockDeclaration+"</declaration>\n");
	        this.createPEAString(pea);
	        writer.write("</template>\n"+
	        		
	        		"<template>"+
	        "<name>check</name> "+
	        "<parameter>urgent chan &amp;dlock</parameter> "+
	        "<declaration>bool err;</declaration> "+
	        "<location id='id8' x='-48' y='56' /> "+
	        "<location id='id9' x='56' y='80' /> "+
	        "<location id='id10' x='40' y='230'>"+
	        "<name x='30' y='200'>initialState</name> "+
	        "</location>"+
	        "<init ref='id10' /> "+
	        "<transition>"+
	        "<source ref='id8' /> "+
	        "<target ref='id8' /> "+
	        "<nail x='-56' y='48' /> "+
	        "<nail x='-32' y='-16' /> "+
	        "<nail x='-8' y='32' /> "+
	        "</transition>"+
	        "<transition>"+
	        "<source ref='id9' /> "+
	        "<target ref='id8' /> "+
	        "<label kind='synchronisation' x='-24' y='40'>dlock?</label> "+
	        "<label kind='assignment' x='-56' y='68'>err:=1</label> "+
	        "</transition>"+
	        "<transition>"+
	        "<source ref='id9' /> "+
	        "<target ref='id9' /> "+
	        "<nail x='104' y='32' /> "+
	        "<nail x='128' y='88' /> "+
	        "</transition>"+
	        "<transition>"+
	        "<source ref='id10' /> "+
	        "<target ref='id9' /> "+
	        "<label kind='assignment' x='-12' y='155'>err:=0</label> "+
	        "</transition>"+
	        "</template>"+
	        		
	        		"<system>urgent chan dlock; " +shortName+"1 = "+shortName+"(dlock); Chk1 = check(dlock);"+
	        		"system "+ shortName+"1, Chk1;</system>\n"+
	                "</nta>");
	        writer.flush();
	        writer.close();
        
        }catch(Exception e) {
            System.out.println("Errors writing the Uppaal representation of pea");
            e.printStackTrace();
        }
        System.out.println("Writing Uppaal representation took "+(System.currentTimeMillis()-actTime)+"ms");
        System.out.println("Computed "+(--this.dnfCount)+" disjunctive normalforms");
        System.out.println("Added: "+(pea.getInit().length)+" further transitions to initial states");
        System.out.println("Deleted: "+(this.deletedSelfloops)+" selfloops without clock reset");
        System.out.println("The transformed PEA has "+(pea.getPhases().length)+" phases");
        
    }

}
