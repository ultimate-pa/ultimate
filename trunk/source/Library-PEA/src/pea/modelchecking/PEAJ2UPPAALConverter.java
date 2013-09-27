/* $Id: PEAJ2UPPAALConverter.java 401 2009-07-02 08:01:53Z jfaber $ 
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

import java.util.ArrayList;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import org.apache.log4j.Logger;
import org.apache.xerces.dom.DocumentImpl;
import org.w3c.dom.Document;
import org.w3c.dom.Element;

import pea.CDD;
import pea.Phase;
import pea.PhaseEventAutomata;
import pea.Transition;

import pea.Decision;
import pea.RangeDecision;

/**
 * @author Roland Meyer
 * 
 * Generates a Uppaal-readable XML-Document for a given net of PEAs. Clocks are
 * not generated automatically and need to be added by hand. Document type
 * definition of Uppaal-files needs to be added by hand.
 * String for detecting final states is static.
 * 
 * This class is a prototype. PEAs should be checked using ARMC.
 */
public class PEAJ2UPPAALConverter {

    protected static final String DEFAULT_LOGGER = "PEAJ2XMLConverter";
    protected static final String FINAL_REGEX = "(.*)FINAL(.*)";

    protected Logger logger = null;

    protected Document document = null;

    protected ArrayList events = null;
    protected ArrayList clocks = null;
    protected ArrayList variables = null;
    private   ArrayList<String> finalStates = new ArrayList<String>();

    public PEAJ2UPPAALConverter(String loggerName) {
        if (loggerName.equals("")) {
            this.logger = Logger.getLogger(PEAJ2XMLConverter.DEFAULT_LOGGER);
        } else {
            this.logger = Logger.getLogger(loggerName);
        }

        this.clocks = new ArrayList();
        this.events = new ArrayList();
        this.variables = new ArrayList();
    }

    public PEAJ2UPPAALConverter() {
        this("");
    }

    public Document convert(PhaseEventAutomata[] peas) {
        if (peas.length == 0) {
            throw new RuntimeException(
                    "The array of peas is not allowed to be empty");
        }

        this.document = new DocumentImpl();

        Element peaNetNode = this.document.createElement("nta");
        Element declNode = this.document.createElement("declaration");
        declNode.appendChild(this.document.createTextNode("clock timer;"));
        peaNetNode.appendChild(declNode);
        this.document.appendChild(peaNetNode);

        for (int i = 0; i < peas.length; i++) {
            this.logger.info("Trying to create peaNode " + i);
            Element actPEANode = this.createPhaseEventAutomaton(peas[i]);
            this.logger.info("Creating peaNode " + i + " successful");
            peaNetNode.appendChild(actPEANode);
        }
	String system = peas[0].getName();
        Element systemNode = this.document.createElement("system");
        systemNode.appendChild(this.document.createTextNode("system "
                + system + ";"));
        peaNetNode.appendChild(systemNode);
        StringBuffer anfrage = new StringBuffer("A[]!(");
	String delim = "";
        for (String state : finalStates ) {
            anfrage.append(delim).append(system).append(".").append(state);
	    delim = "||";
        }
	anfrage.append(")");
        System.out.println(anfrage.toString());
        return this.document;
    }

    protected Element createPhaseEventAutomaton(PhaseEventAutomata pea) {
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

        Element peaNode = this.document.createElement("template");
        Element nameNode = this.document.createElement("name");
        nameNode.appendChild(this.document.createTextNode(pea.getName()));
        peaNode.appendChild(nameNode);

        List<Element> allTransitionNodes = new ArrayList<Element>();
        Phase[] phases = pea.getPhases();
        HashMap<String,Element> phaseNodes = new HashMap<String,Element>();
        for (int i = 0; i < phases.length; i++) {
            Element actPhaseNode = this.createPhaseNode(phases[i]);
            peaNode.appendChild(actPhaseNode);
            phaseNodes.put(phases[i].getName(), actPhaseNode);

            List transitions = phases[i].getTransitions();
            Iterator transitionsIterator = transitions.iterator();
            while (transitionsIterator.hasNext()) {
                Transition actTransition = (Transition) transitionsIterator
                        .next();
                Element[] actTransitionNode = 
		    createTransitionNodes(actTransition);
		for (int j = 0; j < actTransitionNode.length; j++)
		    allTransitionNodes.add(actTransitionNode[j]);
            }
        }

        Phase[] initialPhases = pea.getInit();
        for (int i = 0; i < initialPhases.length; i++) {
            Element initNode = this.document.createElement("init");
            initNode.setAttribute("ref", initialPhases[i].getName());
            peaNode.appendChild(initNode);
        }
        Iterator transIter = allTransitionNodes.iterator();
        while (transIter.hasNext()) {
            Element transitionNode = (Element) transIter.next();
            peaNode.appendChild(transitionNode);

        }
        return peaNode;
    }

    /**
     * Abstracts all information except timings from the given CDD.
     */
    private CDD abstractCDD(CDD cdd) {
	CDD[] children = cdd.getChilds();
	if (children == null) /* true / false node */
	    return cdd;
	Decision d = cdd.getDecision();
	for (int i = 0; i < children.length; i++)
	    children[i] = abstractCDD(children[i]);
	if (d instanceof RangeDecision) {
	    return CDD.create(d, children);
	} else {
	    /* abstract from decision */
	    CDD result = CDD.FALSE;
	    for (int i = 0; i < children.length; i++)
		result = result.or(children[i]);
	    return result;
	}
    }
    private String[] cdd2dnf(CDD cdd) {
	/* first abstract node */
	cdd = abstractCDD(cdd);
	if (cdd == CDD.FALSE)
	    return new String[0];
	if (cdd == CDD.TRUE)
	    return new String[] { "true" };

	Decision d = cdd.getDecision();
	CDD[] children = cdd.getChilds();
	List<String> dnf = new ArrayList<String>();
	for (int i = 0; i < children.length; i++) {
	    if (children[i] == CDD.FALSE)
		continue;
	    if (children[i] == CDD.TRUE) {
		dnf.add(d.toUppaalString(i));
	    } else {
		String[] childDNF = cdd2dnf(children[i]);
		if (!children[i].implies(cdd)) {
		    String prefix = d.toUppaalString(i)
			+ " &amp;&amp; ";
		    for (int j = 0; j < childDNF.length; j++) {
			childDNF[j] = prefix.concat(childDNF[j]);
		    }
		}
		for (int j = 0; j < childDNF.length; j++) {
		    dnf.add(childDNF[j]);
		}
	    }
	}
	return (String[]) dnf.toArray(new String[0]);
    }

    protected Element[] createTransitionNodes(Transition transition) {
        String source = transition.getSrc().getName();
        String target = transition.getDest().getName();
        if (source.equals("") || target.equals("")) {
            throw new RuntimeException(
                    "Source and target of a transition are not allowed to be empty");
        }
	String[] guards = cdd2dnf(transition.getGuard());
	String[] resets = transition.getResets();
	Element[] transNodes = new Element[guards.length];
	for (int i = 0; i < guards.length; i++) {
	    Element transitionNode = this.document.createElement("transition");
	    Element sourceNode = this.document.createElement("source");
	    Element targetNode = this.document.createElement("target");
	    transitionNode.appendChild(sourceNode);
	    transitionNode.appendChild(targetNode);
	    sourceNode.setAttribute("ref", source);
	    targetNode.setAttribute("ref", target);
	    
	    Element guardNode = this.document.createElement("label");
	    guardNode.setAttribute("kind", "guard");
	    guardNode.appendChild(this.document.createTextNode
				  (guards[i] + " &amp;&amp; timer &gt; 0"));
	    transitionNode.appendChild(guardNode);

	    StringBuffer assignment = new StringBuffer();
	    
	    Element actResetNode = this.document.createElement("label");
	    actResetNode.setAttribute("kind", "assignment");
	    
	    for (int j = 0; j < resets.length; j++) {
		assignment.append(resets[j]).append(":=0, ");
	    }
	    assignment.append("timer:=0");
	    actResetNode.appendChild(this.document.createTextNode(assignment
								  .toString()));
	    transitionNode.appendChild(actResetNode);
	    transNodes[i] = transitionNode;
	}
	return transNodes;
    }

    protected Element createPhaseNode(Phase phase) {
        Element phaseNode = this.document.createElement("location");
        phaseNode.setAttribute("id", phase.getName());

        Element nameNode = this.document.createElement("name");
	nameNode.appendChild(this.document.createTextNode(phase.getName()));
        if (phase.getName().matches(PEAJ2UPPAALConverter.FINAL_REGEX)) {
	    finalStates.add(phase.getName());
        }
        phaseNode.appendChild(nameNode);
        Element clockInvariantNode = this.document.createElement("label");
        clockInvariantNode.setAttribute("kind", "invariant");

        if (phase.getClockInvariant() != CDD.TRUE) {
	    String[] clockInv = cdd2dnf(phase.getClockInvariant());
	    if (clockInv.length != 1) 
		throw new IllegalArgumentException
		    ("Non-convex clock invariant: "
		     + phase.getClockInvariant());
            clockInvariantNode.appendChild
		(document.createTextNode(clockInv[0]));
            phaseNode.appendChild(clockInvariantNode);
        }

        return phaseNode;
    }

}
