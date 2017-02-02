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
package de.uni_freiburg.informatik.ultimate.lib.pea.modelchecking;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;

import org.apache.xerces.dom.DocumentImpl;
import org.w3c.dom.Document;
import org.w3c.dom.Element;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.lib.pea.CDD;
import de.uni_freiburg.informatik.ultimate.lib.pea.Decision;
import de.uni_freiburg.informatik.ultimate.lib.pea.Phase;
import de.uni_freiburg.informatik.ultimate.lib.pea.PhaseEventAutomata;
import de.uni_freiburg.informatik.ultimate.lib.pea.RangeDecision;
import de.uni_freiburg.informatik.ultimate.lib.pea.Transition;

/**
 * @author Roland Meyer
 *         Generates a Uppaal-readable XML-Document for a given net of PEAs. Clocks are
 *         not generated automatically and need to be added by hand. Document type
 *         definition of Uppaal-files needs to be added by hand.
 *         String for detecting final states is static.
 *         This class is a prototype. PEAs should be checked using ARMC.
 */
public class PEAJ2UPPAALConverter {
	
	protected static final String DEFAULT_LOGGER = "PEAJ2XMLConverter";
	protected static final String FINAL_REGEX = "(.*)FINAL(.*)";
	
	protected ILogger logger = null;
	
	protected Document document = null;
	
	protected ArrayList<?> events = null;
	protected ArrayList<?> clocks = null;
	protected ArrayList<?> variables = null;
	private final ArrayList<String> finalStates = new ArrayList<>();
	
	public PEAJ2UPPAALConverter(final String loggerName) {
		if (loggerName.equals("")) {
			logger = ILogger.getLogger(PEAJ2XMLConverter.DEFAULT_LOGGER);
		} else {
			logger = ILogger.getLogger(loggerName);
		}
		
		clocks = new ArrayList<>();
		events = new ArrayList<>();
		variables = new ArrayList<>();
	}
	
	public PEAJ2UPPAALConverter() {
		this("");
	}
	
	public Document convert(final PhaseEventAutomata[] peas) {
		if (peas.length == 0) {
			throw new RuntimeException(
					"The array of peas is not allowed to be empty");
		}
		
		document = new DocumentImpl();
		
		final Element peaNetNode = document.createElement("nta");
		final Element declNode = document.createElement("declaration");
		declNode.appendChild(document.createTextNode("clock timer;"));
		peaNetNode.appendChild(declNode);
		document.appendChild(peaNetNode);
		
		for (int i = 0; i < peas.length; i++) {
			logger.info("Trying to create peaNode " + i);
			final Element actPEANode = createPhaseEventAutomaton(peas[i]);
			logger.info("Creating peaNode " + i + " successful");
			peaNetNode.appendChild(actPEANode);
		}
		final String system = peas[0].getName();
		final Element systemNode = document.createElement("system");
		systemNode.appendChild(document.createTextNode("system "
				+ system + ";"));
		peaNetNode.appendChild(systemNode);
		final StringBuffer anfrage = new StringBuffer("A[]!(");
		String delim = "";
		for (final String state : finalStates) {
			anfrage.append(delim).append(system).append(".").append(state);
			delim = "||";
		}
		anfrage.append(")");
		System.out.println(anfrage.toString());
		return document;
	}
	
	protected Element createPhaseEventAutomaton(final PhaseEventAutomata pea) {
		if (pea.getPhases().length == 0) {
			throw new RuntimeException(
					"PEA with phase count = 0 is not allowed");
		}
		if (pea.getInit().length == 0) {
			throw new RuntimeException(
					"PEA with initial phase count = 0 is not allowed");
		}
		
		clocks.clear();
		events.clear();
		variables.clear();
		
		final Element peaNode = document.createElement("template");
		final Element nameNode = document.createElement("name");
		nameNode.appendChild(document.createTextNode(pea.getName()));
		peaNode.appendChild(nameNode);
		
		final List<Element> allTransitionNodes = new ArrayList<>();
		final Phase[] phases = pea.getPhases();
		final HashMap<String, Element> phaseNodes = new HashMap<>();
		for (int i = 0; i < phases.length; i++) {
			final Element actPhaseNode = createPhaseNode(phases[i]);
			peaNode.appendChild(actPhaseNode);
			phaseNodes.put(phases[i].getName(), actPhaseNode);
			
			final List<?> transitions = phases[i].getTransitions();
			final Iterator<?> transitionsIterator = transitions.iterator();
			while (transitionsIterator.hasNext()) {
				final Transition actTransition = (Transition) transitionsIterator
						.next();
				final Element[] actTransitionNode =
						createTransitionNodes(actTransition);
				for (int j = 0; j < actTransitionNode.length; j++) {
					allTransitionNodes.add(actTransitionNode[j]);
				}
			}
		}
		
		final Phase[] initialPhases = pea.getInit();
		for (int i = 0; i < initialPhases.length; i++) {
			final Element initNode = document.createElement("init");
			initNode.setAttribute("ref", initialPhases[i].getName());
			peaNode.appendChild(initNode);
		}
		final Iterator<Element> transIter = allTransitionNodes.iterator();
		while (transIter.hasNext()) {
			final Element transitionNode = transIter.next();
			peaNode.appendChild(transitionNode);
			
		}
		return peaNode;
	}
	
	/**
	 * Abstracts all information except timings from the given CDD.
	 */
	private CDD abstractCDD(final CDD cdd) {
		final CDD[] children = cdd.getChilds();
		if (children == null) {
			return cdd;
		}
		final Decision d = cdd.getDecision();
		for (int i = 0; i < children.length; i++) {
			children[i] = abstractCDD(children[i]);
		}
		if (d instanceof RangeDecision) {
			return CDD.create(d, children);
		}
		/* abstract from decision */
		CDD result = CDD.FALSE;
		for (int i = 0; i < children.length; i++) {
			result = result.or(children[i]);
		}
		return result;
	}
	
	private String[] cdd2dnf(CDD cdd) {
		/* first abstract node */
		cdd = abstractCDD(cdd);
		if (cdd == CDD.FALSE) {
			return new String[0];
		}
		if (cdd == CDD.TRUE) {
			return new String[] { "true" };
		}
		
		final Decision d = cdd.getDecision();
		final CDD[] children = cdd.getChilds();
		final List<String> dnf = new ArrayList<>();
		for (int i = 0; i < children.length; i++) {
			if (children[i] == CDD.FALSE) {
				continue;
			}
			if (children[i] == CDD.TRUE) {
				dnf.add(d.toUppaalString(i));
			} else {
				final String[] childDNF = cdd2dnf(children[i]);
				if (!children[i].implies(cdd)) {
					final String prefix = d.toUppaalString(i)
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
		return dnf.toArray(new String[dnf.size()]);
	}
	
	protected Element[] createTransitionNodes(final Transition transition) {
		final String source = transition.getSrc().getName();
		final String target = transition.getDest().getName();
		if (source.equals("") || target.equals("")) {
			throw new RuntimeException(
					"Source and target of a transition are not allowed to be empty");
		}
		final String[] guards = cdd2dnf(transition.getGuard());
		final String[] resets = transition.getResets();
		final Element[] transNodes = new Element[guards.length];
		for (int i = 0; i < guards.length; i++) {
			final Element transitionNode = document.createElement("transition");
			final Element sourceNode = document.createElement("source");
			final Element targetNode = document.createElement("target");
			transitionNode.appendChild(sourceNode);
			transitionNode.appendChild(targetNode);
			sourceNode.setAttribute("ref", source);
			targetNode.setAttribute("ref", target);
			
			final Element guardNode = document.createElement("label");
			guardNode.setAttribute("kind", "guard");
			guardNode.appendChild(document.createTextNode(guards[i] + " &amp;&amp; timer &gt; 0"));
			transitionNode.appendChild(guardNode);
			
			final StringBuffer assignment = new StringBuffer();
			
			final Element actResetNode = document.createElement("label");
			actResetNode.setAttribute("kind", "assignment");
			
			for (int j = 0; j < resets.length; j++) {
				assignment.append(resets[j]).append(":=0, ");
			}
			assignment.append("timer:=0");
			actResetNode.appendChild(document.createTextNode(assignment
					.toString()));
			transitionNode.appendChild(actResetNode);
			transNodes[i] = transitionNode;
		}
		return transNodes;
	}
	
	protected Element createPhaseNode(final Phase phase) {
		final Element phaseNode = document.createElement("location");
		phaseNode.setAttribute("id", phase.getName());
		
		final Element nameNode = document.createElement("name");
		nameNode.appendChild(document.createTextNode(phase.getName()));
		if (phase.getName().matches(PEAJ2UPPAALConverter.FINAL_REGEX)) {
			finalStates.add(phase.getName());
		}
		phaseNode.appendChild(nameNode);
		final Element clockInvariantNode = document.createElement("label");
		clockInvariantNode.setAttribute("kind", "invariant");
		
		if (phase.getClockInvariant() != CDD.TRUE) {
			final String[] clockInv = cdd2dnf(phase.getClockInvariant());
			if (clockInv.length != 1) {
				throw new IllegalArgumentException("Non-convex clock invariant: "
						+ phase.getClockInvariant());
			}
			clockInvariantNode.appendChild(document.createTextNode(clockInv[0]));
			phaseNode.appendChild(clockInvariantNode);
		}
		
		return phaseNode;
	}
	
}
