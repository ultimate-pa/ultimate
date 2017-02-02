package de.uni_freiburg.informatik.ultimate.lib.pea.modelchecking;

import java.io.BufferedWriter;
import java.io.FileWriter;
import java.io.IOException;
import java.util.List;
import java.util.Vector;

import org.jdom.DocType;
import org.jdom.Document;
import org.jdom.Element;
import org.jdom.JDOMException;
import org.jdom.input.SAXBuilder;
import org.jdom.output.Format;
import org.jdom.output.XMLOutputter;

import de.uni_freiburg.informatik.ultimate.lib.pea.CDD;
import de.uni_freiburg.informatik.ultimate.lib.pea.Phase;
import de.uni_freiburg.informatik.ultimate.lib.pea.PhaseEventAutomata;
import de.uni_freiburg.informatik.ultimate.lib.pea.Transition;



/*
 **
 * The class <code>J2UPPAALConverterDOM</code> transforms a Phase Event automaton object into a xml-File that can be 
 * read via UPPAAL. The difference in J2UPPAALConverter with J2UPPAALConverterDOM is that the J2UPPAALConverterDOM uses 
 * domj.jar (see http://www.jdom.org/downloads/docs.html)
 * UPPAAL changed its input format since version 4.x. Thus use J2UPPAALWriter for UPPAAL versions below 4.x and this
 * Writer for version 4.x and ongoing. 
 * 
 * The algorithm bases on the one given by Jochen Hoenicke in "Combination of Processes, Data, and Time".
 * 1) if the pea has more than one initial state s0i, then we need to add a new initial state, with an edge to every s0i
 * (as uppaal allows only one initial state)
 * 2) in the pea, if a state gets active, it has to be active for some time >0. Thus we introduce a clock "timer".
 * "Timer" is reset in every transition and every transition has a guard, that requires "timer >0".
 * 3) the edges are normalized such that each guard is a conjunct of literals.
 * 4) for all edges (p,g,X,p') of the pea: if s(p)&g&(s(p') is unsatisfiable remove this edge
 * 5) remove unreachable locations
 * 6) remove all literals from the guard except clock constraints and set all state invariants to true
 * 7) for all selfloops: if no clock is reset on this selfloop, then remove this selfloop
 * 
 * Note that unfortunately dom throws exceptions if you want to use just "serializer.output(doc, out);" and
 * there are maaaaaaaaaaaaaaaaaaaaaaaaaany elements below "template". Thus we need this horrible code with the direct
 * writing into the stringBuffer :(
 * 
 * @author Amalinda Oertel
 * April 2010
 * 
 * @see J2UPPAALWriter
 */

public class J2UPPAALConverterDOM {

	private final String initialState = "initialState";
	Element templateElem = new Element("template");
	private final Vector<String> disjuncts = new Vector<String>();
	private int dnfCount=1;
	private int transCount = 0;
	
	final XMLOutputter serializer = new XMLOutputter(Format.getPrettyFormat());
	BufferedWriter out; 

	public void create(String file, PhaseEventAutomata pea){
		final String rulesFileName = file;
		Document doc = null;

		final SAXBuilder parser = new SAXBuilder();
		final long actTime = System.currentTimeMillis();

		try {
			doc = parser.build(rulesFileName);
		} catch (final JDOMException e) {
		} catch (final IOException e) {
		}

		doc = new Document();

		try {
			//First we need to simplify some guards
	        pea.simplifyGuards();
	        
	        //Then start transforming into timed transition system + building up the xml
			out = new BufferedWriter(new FileWriter(file));
			out.write("<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n");
			
			//set doctype			
			final DocType doctype = new DocType("nta");
			doctype.setPublicID("-//Uppaal Team//DTD Flat System 1.0//EN");
			doctype.setSystemID("http://www.docs.uu.se/docs/rtmv/uppaal/xml/flat-1_0.dtd");
			doc.addContent(doctype);
			serializer.output(doctype, out);
			
			//set nta
			doc.addContent(new Element("nta"));
			final Element ntaElem = doc.getRootElement();
			out.newLine();
			out.write("<nta>");
			out.newLine();
			
			//set global declaration
			final Element globalDeclarationElem = new Element("declaration");
			ntaElem.addContent(globalDeclarationElem);    	
			serializer.output(globalDeclarationElem, out);
			out.newLine();
			
			ntaElem.addContent(templateElem);
			out.newLine();
			out.write("<template>");
			out.newLine();

			//set template
			//start template def
			final Element templateNameElem = new Element("name");
			templateNameElem.setText(pea.getName());
			templateElem.addContent(templateNameElem);
			serializer.output(templateNameElem, out);
			out.newLine();

			//local declaration 			
			final Element templateDeclarationElem = new Element("declaration");
			final String clockDeclaration = addDeclarationOfClocks(pea);  
			templateDeclarationElem.setText(clockDeclaration);
			templateElem.addContent(templateDeclarationElem);    
			serializer.output(templateDeclarationElem, out);
			out.newLine();
			

			addLocations(pea);
			addInitialRef(pea);
			addInitialTransitions(pea);
			addPEATransitions(pea);
			
			out.write("\n </template> \n");
			//end template def			

			//set system
			final Element systemElem = new Element("system");
			systemElem.setText("system "+pea.getName()+";");
			ntaElem.addContent(systemElem);    			

			serializer.output(systemElem, out);
			out.newLine();
			out.write("</nta>");
			//serializer.output(doc, out);
			out.close();
			
		}
		catch (final IOException e) {
		}
		System.out.println("Writing Uppaal representation took "+(System.currentTimeMillis()-actTime)+"ms");
        System.out.println("Computed "+(--dnfCount)+" disjunctive normalforms");
        System.out.println("The transformed PEA has "+pea.getPhases().length+" phases");
	}

	//get an overview over all Clocks used in the timed transition system
	private String addDeclarationOfClocks(PhaseEventAutomata pea){
		//we add a new clock "timer" to ensure that every state stays active for some time >0
		String clockDeclaration ="clock timer; "; 
		//and (of course) we also add the clocks of the pea
		final int numberOfClocks = pea.getClocks().size();
		for (int i=0; i<numberOfClocks; i++){
			clockDeclaration = clockDeclaration + "clock "+pea.getClocks().get(i)+"; ";
		}
		return clockDeclaration;
	}

	//Uppaal supports only one initial state; Thus, if a pea has more than one initial state, 
	//we introduce a new state "initialState"
	private void addInitialRef(PhaseEventAutomata pea) throws IOException{
		final Phase[] init = pea.getInit();
		//the following case should never occur if the pea was properly built, but you can never be sure...
		if (init.length <=0){
			System.out.println("ERROR: The pea has no init state");
		}
		//if the PEA has only one init state, then we do not need the further initialState

		if (init.length ==1){
			final Element initRef = new Element("init");
			initRef.setAttribute("ref", init[0].getName());
			templateElem.addContent(initRef);
			serializer.output(initRef, out);
		}
		else //we need the further init state
		{	    		
			final Element initRef = new Element("init");
			initRef.setAttribute("ref", initialState);
			templateElem.addContent(initRef);  
			serializer.output(initRef, out);
			out.newLine();
		}
	}



	private void addLocations(PhaseEventAutomata pea) throws IOException{
		final Phase[] init = pea.getInit();
		//add all locations of the pea
		final Phase[] phases = pea.getPhases();  
		for(int i=0; i<phases.length; i++) {
			final Phase phase = phases[i];
			final Element location = new Element("location");
			location.setAttribute("id", phase.getName());	
			final Element tempLocName = new Element("name");
			tempLocName.setText(phase.getName());
			location.addContent(tempLocName);

			if(phase.getClockInvariant()!=CDD.TRUE) {
				final String[]formula = getDisjuncts(phase.getClockInvariant());
				String clockInvariant = formula[0];
				for (int j=1; j<formula.length; j++){
					clockInvariant = clockInvariant + " && " + formula[j];
				}
				final Element tempLocLabel = new Element("label");
				tempLocLabel.setAttribute("kind", "invariant");
				tempLocLabel.setText(clockInvariant); 
				location.addContent(tempLocLabel);
			}			
			templateElem.addContent(location);
			serializer.output(location, out);
			out.newLine();
		}
		//check whether a further initial state is needed
		if (init.length > 1){
			//this further init state shall be committed, thus, there is no delay allowed in this state
			final Element initLocation = new Element("location");
			initLocation.setAttribute("id", initialState);
			final Element locationName = new Element("name");
			locationName.setText(initialState);
			final Element locationCommit = new Element("committed");
			templateElem.addContent(initLocation);
			initLocation.addContent(locationName);
			initLocation.addContent(locationCommit);
			serializer.output(initLocation, out);
			out.newLine();
		}

	}

	//add the transitions of the pea
	private void addPEATransitions(PhaseEventAutomata pea) throws IOException {

		final Phase[] phases = pea.getPhases();  
		final Vector<Transition> transitions = new Vector<Transition>();   

		for(int i=0; i<phases.length; i++) {
			final Phase phase = phases[i];
			transitions.addAll(phase.getTransitions());
		}    

		transCount = transitions.size();
		for (int j=0; j<transCount; j++){
			final Transition trans = transitions.elementAt(j);
			createPEATransitionString(trans);
		}       

	}

	private void createPEATransitionString(Transition transition) throws IOException{
		final String[] disjuncts = getDisjuncts(transition.getGuard());        
		final String[] resets = transition.getResets();
		final StringBuffer assignment = new StringBuffer();

		for (int i = 0; i < resets.length; i++) {
			assignment.append(resets[i]).append(":=0, ");
		}
		assignment.append("timer:=0");

		for(int i=0; i<disjuncts.length; i++) {

			final String source = transition.getSrc().getName();
			final String destination = transition.getDest().getName();

			if(source.matches(destination)&& (resets.length<=0)){
				//selfloops in which no clock is reset do not need to be transfered to the uppaal model
			}
			else
			{
				final Element transitionEl = new Element("transition");
				final Element sourceEl = new Element("source");
				final Element targetEl = new Element("target");
				final Element labelElGuard = new Element("label");
				final Element labelElAssignment = new Element("label");

				sourceEl.setAttribute("ref", source);
				targetEl.setAttribute("ref", destination);
				labelElGuard.setAttribute("kind", "guard");
				labelElAssignment.setAttribute("kind", "assignment");

				if (disjuncts[i].isEmpty()){
					labelElGuard.setText("timer > 0");
				}
				else 
				{
					labelElGuard.setText(disjuncts[i]+" && timer > 0");
				} 
				labelElAssignment.setText(assignment.toString());

				transitionEl.addContent(sourceEl);
				transitionEl.addContent(targetEl);
				transitionEl.addContent(labelElGuard);
				transitionEl.addContent(labelElAssignment);	
				//templateElem.addContent(transitionEl);
				serializer.output(transitionEl, out);
				out.newLine();
				out.flush();
			}
		}
	}

	private void addInitialTransitions(PhaseEventAutomata pea) throws IOException {
		final Phase[] init = pea.getInit();

		//if the PEA has only one init state, then we do not need the further initialState, and thus no further transitions
		//otherwise add transitions from initialState to every init state and if this init state has a clock invariant
		//then reset the clock
		if (init.length >1)
		{  		
			for(int i=0; i<init.length; i++) { //for all init states

				final Phase initState = init[i];
				final CDD initClock = initState.getClockInvariant();
				final List<String> peaClocks = pea.getClocks();
				//What clocks are part of the clock invariant of the initial state    		
				final String reset = getClocksToReset(initState, peaClocks);  

				final Element transitionEl = new Element("transition");
				final Element sourceEl = new Element("source");
				final Element targetEl = new Element("target");
				final Element labelElAssignment = new Element("label");

				sourceEl.setAttribute("ref", initialState);
				targetEl.setAttribute("ref", initState.getName());
				transitionEl.addContent(sourceEl);
				transitionEl.addContent(targetEl);

				if (initClock != CDD.TRUE){
					labelElAssignment.setAttribute("kind", "assignment");
					labelElAssignment.setText(reset);
					transitionEl.addContent(labelElAssignment);	
				}    	       
				templateElem.addContent(transitionEl);
				serializer.output(transitionEl, out);
				out.newLine();
				out.flush();

			}    	    	
		}
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
					reset = reset + ", "+peaClocks.get(j) + ":= 0 "; // the clocks need to be separated via comma
				}
			}
		}
		return reset;
	}

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

//	private StringBuffer cddToDNF(StringBuffer buf, CDD cdd) {
//		if(cdd == CDD.TRUE) {
//			if(buf.toString().endsWith(" && ")){
//				buf.delete(buf.length()-4, buf.length());
//			}
//			//System.out.println("Adding="+buf.toString());
//			this.disjuncts.add(buf.toString());
//			return buf;
//		} else if (cdd == CDD.FALSE) {
//			return buf;
//		}
//		int numberOfChilds = cdd.getChilds().length;
//		StringBuffer newBuf = new StringBuffer();
//		for(int i=0;i<numberOfChilds;i++) {
//
//			newBuf.append(buf.toString());        
//			newBuf.append(cdd.getDecision().toUppaalStringDOM(i));
//			newBuf.append(" && ");         	     	      
//			this.cddToDNF(newBuf,cdd.getChilds()[i]);
//		}
//		return newBuf;
//	}
	
	private void cddToDNF(StringBuffer buf, CDD cdd) {
        if(cdd == CDD.TRUE) {
            //TODO fix this arghgrmbl implementation (presumably, complete
            //     reimplementation needed)
            if(buf.toString().endsWith(" && ")){
				buf.delete(buf.length()-4, buf.length());
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
            
            newBuf.append(cdd.getDecision().toUppaalStringDOM(i));
            newBuf.append(" && ");
            
            cddToDNF(newBuf,cdd.getChilds()[i]);
        }
    }

	public static void main(String[] args) {
		// TODO Auto-generated method stub

	}


}
