package de.uni_freiburg.informatik.ultimate.lib.pea.modelchecking;

import java.io.FileWriter;
import java.util.Iterator;
import java.util.List;
import java.util.Vector;

import de.uni_freiburg.informatik.ultimate.lib.pea.CDD;
import de.uni_freiburg.informatik.ultimate.lib.pea.EventDecision;
import de.uni_freiburg.informatik.ultimate.lib.pea.Phase;
import de.uni_freiburg.informatik.ultimate.lib.pea.PhaseEventAutomata;
import de.uni_freiburg.informatik.ultimate.lib.pea.Transition;

/**
 * The class <code>J2UPPAALWriterV4</code> transforms a Phase Event automaton object into a xml-File that can be read via UPPAAL.
 * UPPAAL changed its input format since version 4.x. Thus use J2UPPAALWriter for UPPAAL versions below 4.x and this
 * Writer for version 4.x and ongoing. 
 * 
 * @author Amalinda Oertel
 * April 2010
 * 
 * @see J2UPPAALWriter
 */

public class J2UPPAALWriterV4 {
private final Vector<String> disjuncts = new Vector<String>();
    
    private int dnfCount=1;
    private int transCount = 0;
    private final String initialState = "initialState";
    
    public String[] getDisjuncts(CDD cdd) {
        disjuncts.clear();
        System.out.println("Computing dnf "+dnfCount+"/"+transCount);
        dnfCount++;
        cddToDNF(new StringBuffer(), cdd);
        
        final int disjunctCount = disjuncts.size();
        final String[] strings = new String[disjunctCount];
        for(int i=0; i<disjunctCount; i++) {
            strings[i] = disjuncts.elementAt(i);
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
            disjuncts.add(buf.toString());
            return;
        } else if (cdd == CDD.FALSE) {
            return;
        }
        for(int i=0;i<cdd.getChilds().length;i++) {
            final StringBuffer newBuf = new StringBuffer();
            newBuf.append(buf.toString());
            
            newBuf.append(cdd.getDecision().toUppaalString(i));
            newBuf.append(" &amp;&amp; ");
            
            cddToDNF(newBuf,cdd.getChilds()[i]);
        }
    }
    
    private StringBuffer cddToDNF_NEU(StringBuffer buf, CDD cdd) {
        if(cdd == CDD.TRUE) {
            //TODO fix this arghgrmbl implementation (presumably, complete
            //     reimplementation needed)
            if(buf.toString().endsWith(" &amp;&amp; ")){
                buf.delete(buf.length()-12, buf.length());
            }
            //System.out.println("Adding="+buf.toString());
            disjuncts.add(buf.toString());
            return buf;
        } else if (cdd == CDD.FALSE) {
            return buf;
        }
        final StringBuffer newBuf = new StringBuffer();
        for(int i=0;i<cdd.getChilds().length;i++) {
        	
        	newBuf.append(buf.toString());
        
        	newBuf.append(cdd.getDecision().toUppaalString(i));
        	newBuf.append(" &amp;&amp; ");
        
        	cddToDNF(newBuf,cdd.getChilds()[i]);
        	
        }
        return newBuf;
    }
    
    //Uppaal supports only one initial state; Thus, if a pea has more than one initial state, 
    //we introduce a new state "initState" and an edge from this "initState" to all initial states of the PEA
    private String initialStates(PhaseEventAutomata pea){
    	final StringBuffer buf = new StringBuffer();
    	final Phase[] init = pea.getInit();
    	
    	//if the PEA has only one init state, then we do not need the further initialState
    	if (init.length <2){
    		buf.append("<init ref = \""+init[0].getName()+"\"/>\n");
    	}
    	else //we need the further init state
    	{
    		buf.append("<init ref = \""+initialState +"\"/>\n");
    	}
    	return buf.toString();
    }
    
    private String getClocksToReset(Phase state, List<String> peaClocks){
    	final String initClockString = state.getClockInvariant().toString();
    	Boolean firstClock = true;
		//List<String> peaClocks = pea.getClocks();
		String reset = ""; 
		for (int j =0; j<peaClocks.size(); j++){
			if (initClockString.contains(peaClocks.get(j))){
				if (firstClock){ //the end of the string may not end with a comma, otherwise uppaal will grump
					reset = peaClocks.get(j) + ":= 0 ";
					firstClock = false;
				}
				else {
					reset = ", "+peaClocks.get(j) + ":= 0 "; // the clocks need to be separated via comma
				}
			}
		}
    return reset;
    }
    
    private String initialTransitions(PhaseEventAutomata pea){
    	final StringBuffer buf = new StringBuffer();
    	final Phase[] init = pea.getInit();
    	
    	//if the PEA has only one init state, then we do not need the further initialState
    	if (init.length >=2)
    	{
    		//if init.length <2 nothing needs to be done, as we use the initial state by PEA
    		for(int i=0; i<init.length; i++) {
    			
    			final Phase initState = init[i];
    			final CDD initClock = initState.getClockInvariant();
    			String reset;
    			
    			//What clocks are part of the clock invariant of the initial state?
    			final List<String> peaClocks = pea.getClocks();
    			reset = getClocksToReset(initState, peaClocks);
    			
    	       buf.append("<transition>\n"+
    	       "  <source ref = \""+initialState+"\"/>\n"+
    	       "  <target ref = \""+initState.getName()+"\"/>\n");
    	       //if the PEA inital state has a clock invariant, then we need to set the clock(s) to zero
    	       if (initClock != CDD.TRUE){
    	    	   buf.append(" <label kind = \"assignment\">"+reset+"</label>\n");
    	       }    	       
    	        //there is no guard for an initial state
    	       buf.append("</transition>\n");
    	        
    			
            }
    	    		//buf.append("<init ref = \""+initialState+"\"/>\n");
    	}
    	return buf.toString();
    }
    
    private String createPEAString(PhaseEventAutomata pea) {
        final StringBuffer buf = new StringBuffer();
        final Phase[] phases = pea.getPhases();
        final int numberOfInitStates = pea.getInit().length;
        final Vector<Transition> transitions = new Vector<Transition>();
        
      //if there are more than one initial state in the pea, we need a further initial state
        //this further init state shall be committed, thus, there is no delay allowed in this state
        if (numberOfInitStates > 1){
        buf.append("<location id = \""+initialState+"\">\n"+
                "  <name>"+initialState+"</name>\n <committed/>\n </location>\n");
        }
        for(int i=0; i<phases.length; i++) {
            buf.append(createPEAPhaseString(phases[i]));
            transitions.addAll(phases[i].getTransitions());
        }
        buf.append(initialStates(pea));
        buf.append(initialTransitions(pea));
        //Phase[] init = pea.getInit();
        //buf.append("<init ref = \""+init[0].getName()+"\"/>");
        transCount = transitions.size();
        final Iterator transIter = transitions.iterator();
        while (transIter.hasNext()) {
            final Transition actTrans = (Transition) transIter.next();
            buf.append(createPEATransitionString(actTrans));
        }
        return buf.toString();
    }
    
    private String createPEAPhaseString(Phase phase) {
        final StringBuffer buf = new StringBuffer();        
        buf.append("<location id = \""+phase.getName()+"\""+">\n"+
                "  <name>"+phase.getName()+"</name>\n");
        if(phase.getClockInvariant()!=CDD.TRUE) {
	    //StringBuffer formula = new StringBuffer();
	    final String[]formula2 = getDisjuncts(phase.getClockInvariant());
	    buf.append("  <label kind = \"invariant\">"+formula2[0]);
	    for (int i=1; i<formula2.length; i++){
	    	 buf.append(" &amp;&amp; "+formula2[i]);
	    }
	    buf.append("</label>\n");
	   
	    //formula = cddToDNF(formula, phase.getClockInvariant());
        //    buf.append("  <label kind = \"invariant\">"+formula.toString()+"</label>\n");
        //}
        
        }
        buf.append("</location>\n");
        return buf.toString();
        }
    
    
    private String createPEATransitionString(Transition transition) {
        final StringBuffer buf = new StringBuffer();
        final String[] disjuncts = getDisjuncts(transition.getGuard());
        
        final String[] resets = transition.getResets();
        final StringBuffer assignment = new StringBuffer();
        for (int i = 0; i < resets.length; i++) {
            assignment.append(resets[i]).append(":=0, ");
        }
        assignment.append("timer:=0");
        
        for(int i=0; i<disjuncts.length; i++) {
            buf.append("<transition>\n"+
            "  <source ref = \""+transition.getSrc().getName()+"\"/>\n"+
            "  <target ref = \""+transition.getDest().getName()+"\"/>\n");
            if (disjuncts[i].isEmpty()){
            	buf.append("  <label kind = \"guard\"> timer &gt; 0 </label>\n");
            }
            else 
            {
            	buf.append("  <label kind = \"guard\">"+disjuncts[i]+" &amp;&amp; timer &gt; 0 </label>\n"); //XML Sonderzeichen &amp; = & 	
            }            
            buf.append("  <label kind = \"assignment\">"+assignment.toString()+"</label>\n"+
            "</transition>\n");
        }
        return buf.toString();
    }
    public void writePEA2UppaalFile(String file, PhaseEventAutomata pea) {
        final long actTime = System.currentTimeMillis();
        try {
        final FileWriter writer = new FileWriter(file);
        String clockDeclaration ="clock timer; \n";
        final int numberOfClocks = pea.getClocks().size();
        for (int i=0; i<numberOfClocks; i++){
        	clockDeclaration = clockDeclaration + "clock "+pea.getClocks().get(i)+"; \n";
        }
        
        writer.write("<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n" +
                     "<!DOCTYPE nta PUBLIC \"-//Uppaal Team//DTD Flat System 1.0//EN\" \"http://www.docs.uu.se/docs/rtmv/uppaal/xml/flat-1_0.dtd\">" +
                     "<nta>\n"+
                     "<declaration>\n"+clockDeclaration+"</declaration>\n" +
                     "<template>\n" +
                     "<name>"+//pea.getName()
                     "DeadlockSystem"+"</name>\n");
        writer.write(createPEAString(pea));
        writer.write("</template>\n"+
                        "<system>system "+//pea.getName()
                        "DeadlockSystem"+";</system>\n"+
                        "</nta>");
        writer.flush();
        writer.close();
        }catch(final Exception e) {
            System.out.println("Errors writing the Uppaal representation of pea");
            e.printStackTrace();
        }
        System.out.println("Writing Uppaal representation took "+(System.currentTimeMillis()-actTime)+"ms");
        System.out.println("Computed "+(--dnfCount)+" disjunctive normalforms");
        System.out.println("The transformed PEA has "+pea.getPhases().length+" phases");
    }
    
    public static void main(String[] param) {
        final CDD a = EventDecision.create("a");
        final CDD b = EventDecision.create("b");
        final CDD c = EventDecision.create("c");
        final CDD e = EventDecision.create("e");
        
        final CDD temp = a.and(b.or(c).and(e.negate()));
        System.out.println(temp.toString());
        final J2UPPAALWriter writer = new J2UPPAALWriter();
        final String[] result = writer.getDisjuncts(temp);
        System.out.println("Result = ");
        for(int i=0; i<result.length; i++) {
            System.out.println(result[i]);
        }
        //private static final String PATH = "C:/Documents and Settings/oea1lr/My Documents/Test/PEA/peatoolkit-0.89b-src/";
        try {
            final PEAXML2JConverter xml2JConverter = new PEAXML2JConverter(false);
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
            final PhaseEventAutomata[] propertyPeas = xml2JConverter
                    .convert("C:/Documents and Settings/oea1lr/My Documents/Test/PEA/peatoolkit-0.89b-src/src/pea/modelchecking/CaseStudy/Property0.xml");
            for (int i = 0; i < propertyPeas.length; i++) {
                toUppaal = toUppaal.parallel(propertyPeas[i]);
            }
            final J2UPPAALWriter j2uppaalWriter = new J2UPPAALWriter();
            j2uppaalWriter.writePEA2UppaalFile("C:/Documents and Settings/oea1lr/My Documents/Test/PEA/peatoolkit-0.89b-src/src/pea/modelchecking/CaseStudy/toCheck.xml", toUppaal);
        }catch(final Exception ex) {
            ex.printStackTrace();
        }
    }
}
