/* $Id: J2UPPAALWriter.java 326 2008-08-01 16:41:13Z jfaber $ 
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
import java.util.Iterator;
import java.util.Vector;

import pea.CDD;
import pea.EventDecision;
import pea.Phase;
import pea.Transition;
import pea.PhaseEventAutomata;

/**
 * @author roland
 *
 * Generates UPPAAL Output for peas. Computes DNF for guards.
 */
public class J2UPPAALWriter {
    
    private Vector<String> disjuncts = new Vector<String>();
    
    private int dnfCount=1;
    private int transCount = 0;
    
    public String[] getDisjuncts(CDD cdd) {
        this.disjuncts.clear();
        System.out.println("Computing dnf "+dnfCount+"/"+this.transCount);
        dnfCount++;
        this.cddToDNF(new StringBuffer(), cdd);
        
        int disjunctCount = this.disjuncts.size();
        String[] strings = new String[disjunctCount];
        for(int i=0; i<disjunctCount; i++) {
            strings[i] = (String) this.disjuncts.elementAt(i);
        }
        
        return strings;
    }
    
    private void cddToDNF(StringBuffer buf, CDD cdd) {
        if(cdd == CDD.TRUE) {
            //TODO fix this arghgrmbl implementation (presumably, complete
            //     reimplementation needed)
            if(buf.toString().endsWith(" &amp;&amp; ")){
                buf.delete(buf.length()-12, buf.length());
            }
            //System.out.println("Adding="+buf.toString());
            this.disjuncts.add(buf.toString());
            return;
        } else if (cdd == CDD.FALSE) {
            return;
        }
        for(int i=0;i<cdd.getChilds().length;i++) {
            StringBuffer newBuf = new StringBuffer();
            newBuf.append(buf.toString());
            
            newBuf.append(cdd.getDecision().toUppaalString(i));
            newBuf.append(" &amp;&amp; ");
            
            this.cddToDNF(newBuf,cdd.getChilds()[i]);
        }
    }
    
    private String createPEAString(PhaseEventAutomata pea) {
        StringBuffer buf = new StringBuffer();
        Phase[] phases = pea.getPhases();
        Vector<Transition> transitions = new Vector<Transition>();
        for(int i=0; i<phases.length; i++) {
            buf.append(this.createPEAPhaseString(phases[i]));
            transitions.addAll(phases[i].getTransitions());
        }
        Phase[] init = pea.getInit();
        buf.append("<init ref = \""+init[0].getName()+"\"/>");
        this.transCount = transitions.size();
        Iterator transIter = transitions.iterator();
        while (transIter.hasNext()) {
            Transition actTrans = (Transition) transIter.next();
            buf.append(this.createPEATransitionString(actTrans));
        }
        return buf.toString();
    }
    
    private String createPEAPhaseString(Phase phase) {
        StringBuffer buf = new StringBuffer();
        buf.append("<location id = \""+phase.getName()+"\""+">\n"+
                "  <name>"+phase.getName()+"</name>\n");
        if(phase.getClockInvariant()!=CDD.TRUE) {
	    StringBuffer formula = new StringBuffer();
	    cddToDNF(formula, phase.getClockInvariant());
            buf.append("  <label kind = \"invariant\">"+formula.toString()+"</label>\n");
        }
        buf.append("</location>\n");
        return buf.toString();
    }
    
    private String createPEATransitionString(Transition transition) {
        StringBuffer buf = new StringBuffer();
        String[] disjuncts = this.getDisjuncts(transition.getGuard());
        
        String[] resets = transition.getResets();
        StringBuffer assignment = new StringBuffer();
        for (int i = 0; i < resets.length; i++) {
            assignment.append(resets[i]).append(":=0, ");
        }
        assignment.append("timer:=0");
        
        for(int i=0; i<disjuncts.length; i++) {
            buf.append("<transition>\n"+
            "  <source ref = \""+transition.getSrc().getName()+"\"/>\n"+
            "  <target ref = \""+transition.getDest().getName()+"\"/>\n"+
            "  <label kind = \"guard\">("+disjuncts[i]+") &amp;&amp; timer &gt; 0</label>\n"+
            "  <label kind = \"assignment\">"+assignment.toString()+"</label>\n"+
            "</transition>\n");
        }
        return buf.toString();
    }
    public void writePEA2UppaalFile(String file, PhaseEventAutomata pea) {
        long actTime = System.currentTimeMillis();
        try {
        FileWriter writer = new FileWriter(file);
        writer.write("<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n" +
                     "<!DOCTYPE nta PUBLIC \"-//Uppaal Team//DTD Flat System 1.0//EN\" \"http://www.docs.uu.se/docs/rtmv/uppaal/xml/flat-1_0.dtd\">" +
                     "<nta>\n"+
                     "<declaration>clock timer,ComNWDC1_c2,ComNWDC3_c2,pea0_X1, Train1_c2,Train2_c2,RBCDC_c2;</declaration>\n" +
                     "<template>\n" +
                     "<name>"+//pea.getName()
                     "TrainSystem"+"</name>\n");
        writer.write(this.createPEAString(pea));
        writer.write("</template>\n"+
                        "<system>system "+//pea.getName()
                        "DeadlockSystem"+";</system>\n"+
                        "</nta>");
        writer.flush();
        writer.close();
        }catch(Exception e) {
            System.out.println("Errors writing the Uppaal representation of pea");
            e.printStackTrace();
        }
        System.out.println("Writing Uppaal representation took "+(System.currentTimeMillis()-actTime)+"ms");
        System.out.println("Computed "+(--this.dnfCount)+" disjunctive normalforms");
    }
    
    public static void main(String[] param) {
        CDD a = EventDecision.create("a");
        CDD b = EventDecision.create("b");
        CDD c = EventDecision.create("c");
        CDD e = EventDecision.create("e");
        
        CDD temp = a.and(b.or(c).and(e.negate()));
        System.out.println(temp.toString());
        J2UPPAALWriter writer = new J2UPPAALWriter();
        String[] result = writer.getDisjuncts(temp);
        System.out.println("Result = ");
        for(int i=0; i<result.length; i++) {
            System.out.println(result[i]);
        }
        //private static final String PATH = "C:/Documents and Settings/oea1lr/My Documents/Test/PEA/peatoolkit-0.89b-src/";
        try {
            PEAXML2JConverter xml2JConverter = new PEAXML2JConverter(false);
            PhaseEventAutomata[] systemPeas = xml2JConverter
                    .convert("C:/Documents and Settings/oea1lr/My Documents/Test/PEA/peatoolkit-0.89b-src/src/pea/modelchecking/CaseStudy/Environment.xml");
            PhaseEventAutomata toUppaal = systemPeas[0];
            for (int i = 1; i < systemPeas.length; i++) {
                toUppaal = toUppaal.parallel(systemPeas[i]);
            }
            systemPeas = xml2JConverter.convert("C:/Documents and Settings/oea1lr/My Documents/Test/PEA/peatoolkit-0.89b-src/src/pea/modelchecking/CaseStudy/TrainEmergency.xml");
            for (int i = 0; i < systemPeas.length; i++) {
                toUppaal = toUppaal.parallel(systemPeas[i]);
            }
            systemPeas = xml2JConverter.convert("C:/Documents and Settings/oea1lr/My Documents/Test/PEA/peatoolkit-0.89b-src/src/pea/modelchecking/CaseStudy/TrainReact.xml");
            for (int i = 0; i < systemPeas.length; i++) {
                toUppaal = toUppaal.parallel(systemPeas[i]);
            }
            systemPeas = xml2JConverter.convert("C:/Documents and Settings/oea1lr/My Documents/Test/PEA/peatoolkit-0.89b-src/src/pea/modelchecking/CaseStudy/ComNW.xml");
            for (int i = 0; i < systemPeas.length; i++) {
                toUppaal = toUppaal.parallel(systemPeas[i]);
            }
            systemPeas = xml2JConverter.convert("C:/Documents and Settings/oea1lr/My Documents/Test/PEA/peatoolkit-0.89b-src/src/pea/modelchecking/CaseStudy/RBC.xml");
            for (int i = 0; i < systemPeas.length; i++) {
                toUppaal = toUppaal.parallel(systemPeas[i]);
            }
            PhaseEventAutomata[] propertyPeas = xml2JConverter
                    .convert("C:/Documents and Settings/oea1lr/My Documents/Test/PEA/peatoolkit-0.89b-src/src/pea/modelchecking/CaseStudy/Property0.xml");
            for (int i = 0; i < propertyPeas.length; i++) {
                toUppaal = toUppaal.parallel(propertyPeas[i]);
            }
            J2UPPAALWriter j2uppaalWriter = new J2UPPAALWriter();
            j2uppaalWriter.writePEA2UppaalFile("C:/Documents and Settings/oea1lr/My Documents/Test/PEA/peatoolkit-0.89b-src/src/pea/modelchecking/CaseStudy/toCheck.xml", toUppaal);
        }catch(Exception ex) {
            ex.printStackTrace();
        }
    }
    
}
