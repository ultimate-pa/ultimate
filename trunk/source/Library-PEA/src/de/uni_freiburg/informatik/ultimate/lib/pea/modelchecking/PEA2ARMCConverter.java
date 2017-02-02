/* $Id: PEA2ARMCConverter.java 401 2009-07-02 08:01:53Z jfaber $ 
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

import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Iterator;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.lib.pea.Phase;
import de.uni_freiburg.informatik.ultimate.lib.pea.PhaseEventAutomata;
import de.uni_freiburg.informatik.ultimate.lib.pea.Transition;

@Deprecated
public class PEA2ARMCConverter {

        protected static final String BADSTATENAME_ARMC = "error";  
    
	protected static final String STATE_NAME = "state";

	protected FormulaJ2ARMCConverter formulaConverter = new FormulaJ2ARMCConverter();

	protected FileWriter writer;

	protected List<String> additionalVariables = null;

	protected List<String> additionalTypes = null;

	protected List<String> clocks = null;

	protected String cont = "";

	protected boolean rename = false;

	protected int transCounter = 1;

        protected int numberOfDNFs = 0;

        public void convert(PhaseEventAutomata pea, String file,
                            List<String> addVars, List<String> addTypes)
        {
            convert(pea, file, addVars, addTypes, false);
        }
    
	public void convert(PhaseEventAutomata pea, 
						String file, 
						List<String> addVars,
						List<String> addTypes,
						boolean rename) {
		try {
			this.rename = rename;
			writer = new FileWriter(file);
			additionalVariables = addVars;
			additionalTypes = addTypes;
			clocks = pea.getClocks();

			//this.computeCont();
			computeNumberOfDNFs(pea);
            
			createPhaseEventAutomaton(pea);
			
			writer.flush();
			writer.close();
		} catch (final Exception e) {
			System.out
					.println("Errors writing the TCS-ARMC representation of pea");
			e.printStackTrace();
		}
	}

	protected void createPhaseEventAutomaton(PhaseEventAutomata pea)
			throws IOException {
		if (pea.getPhases().length == 0) {
			throw new RuntimeException(
					"PEA with phase count = 0 is not allowed");
		}
		if (pea.getInit().length == 0) {
			throw new RuntimeException(
					"PEA with initial phase count = 0 is not allowed");
		}

		writer
				.write("% Preamble:\n\n"
						+ ":- multifile r/5,implicit_updates/0,var2names/2,preds/2,cube_size/1,start/1,error/1,refinement/1.\n"
						+ "refinement(inter).\ncube_size(1).\n"
						+ "start(pc(init)).\n" + "error(pc(error)).\n\n\n");

		// Write variable lists
		final StringBuffer variableBuffer = new StringBuffer("");
		final StringBuffer variablePrimedBuffer = new StringBuffer("");
		variableBuffer.append("_len");
		variablePrimedBuffer.append("_lenP");

        for(final String actVariable : additionalVariables){
		    variableBuffer.append(",_" + actVariable);
		    variablePrimedBuffer.append(",_" + actVariable + "P");
        }    
		
        for (final String clock: clocks) {
		    variableBuffer.append(",_" + clock);
		    variablePrimedBuffer.append(",_" + clock + "P");
		}

		writer.write("preds(p(_, data(");
		writer.write(variableBuffer.toString() + ")), []).\n\n");

		// Write Var2Names lists
		writer.write("var2names(p(_, data(" + variableBuffer.toString()
				+ ")),\n   [(_len, 'len')");
		for (final String actVariable : additionalVariables) {
            writer.write(",\n    (_" + actVariable + ", '" + actVariable
                    + "')");
        }
        for (final String clock: clocks) {
            writer.write(",\n    (_" + clock + ", '" + clock
                    + "')");
        }

		writer.write("]).\n\n\n\n");

		// Rename phases if necessary
		final Phase[] phases = pea.getPhases();
		if (rename) {
			int stateCounter = phases.length;
			//this.nameWriter.write("#!/usr/bin/perl -pi\n\n");
			for (int i = 0; i < phases.length; i++) {
				if (!phases[i].getName().equals(SimplifyPEAs.BADSTATESTRING)) {
			//		this.nameWriter.write("  s/"+PEA2TCSJ2XMLConverter.STATE_NAME
			//				+ stateCounter+"/"+phases[i].getName()+"/g;\n");
					phases[i].setName(PEA2TCSJ2XMLConverter.STATE_NAME
							+ stateCounter);
				} else {
					phases[i].setName(PEA2ARMCConverter.BADSTATENAME_ARMC);
				}
				stateCounter--;
			}
		} else {
			for (int i = 0; i < phases.length; i++) {
				if (!phases[i].getName().equals(SimplifyPEAs.BADSTATESTRING)) {
					phases[i].setName("p" + phases[i].getName());
				} else {
					phases[i].setName(PEA2ARMCConverter.BADSTATENAME_ARMC);
				}
			}
		}

		// Create edges to initial phases
		final Phase[] init = pea.getInit();
		for (int i = 0; i < init.length; i++) {
			createInitEdge(init[i], variableBuffer.toString(),
					variablePrimedBuffer.toString());
		}

		// Create transitions
		for (int i = 0; i < phases.length; i++) {
			final List transitions = phases[i].getTransitions();
			final Iterator transIter = transitions.iterator();
			while (transIter.hasNext()) {
				final Transition trans = (Transition) transIter.next();
				createTransitionNode(trans, variableBuffer.toString(),
						variablePrimedBuffer.toString());
			}
            //this.createContTransition(phases[i],variableBuffer.toString(),
            //        variablePrimedBuffer.toString());
		}

	}

/*    protected void createContTransition(Phase phase, String varString, String primedVarString) throws IOException{
        String[] inv = this.compInvP2(phase);
        
        String[] sepContConj = cont.toString().split("/\\\\");

        List<String> primed = new ArrayList<String>();
        List<String> unprimed = new ArrayList<String>();
        this.fillPrimedAndUnprimedLists(sepContConj, primed, unprimed);

        for (int i = 0; i < inv.length; i++) {
            String[] sepInvConj = inv[i].split("/\\\\");

            List<String> primedForSepInvConj = new ArrayList<String>(primed);
            List<String> unprimedForSepInvConj = new ArrayList<String>(unprimed);
            
            this.fillPrimedAndUnprimedLists(sepInvConj, primedForSepInvConj,
                unprimedForSepInvConj);

            this.writeTransition(phase.getName(), phase.getName(), primedForSepInvConj, unprimedForSepInvConj, varString,
                    primedVarString);
        }
    }*/

    protected void createInitEdge(Phase phase, String varString,
			String primedVarString) throws IOException {

		final List<String> initConstraints = new ArrayList<String>();
		//initConstraints.add("_discP = 0");
		initConstraints.add("_lenP > 0");
		if (!clocks.isEmpty()) {
			final Iterator clocksIterator = clocks.iterator();
			while (clocksIterator.hasNext()) {
				final String actClock = (String) clocksIterator.next();
				initConstraints.add("_" + actClock + "' = "+
						    (phase.isStopped(actClock) ? "0" : "_len'"));
			}
		}

		final String[] stateInvDis = formulaConverter.getDisjuncts(true, phase
				.getStateInvariant(), numberOfDNFs);
		final String[] clockInvDis = formulaConverter.getDisjuncts(true, phase
				.getClockInvariant(),numberOfDNFs);
		for (int i = 0; i < stateInvDis.length; i++) {

			final String[] stateInvSplitted = stateInvDis[i].split("/\\\\");
			final List<String> primedForStateInv = new ArrayList<String>();
			fillPrimedAndUnprimedLists(stateInvSplitted, primedForStateInv, new ArrayList<String>());
			
			for (int j = 0; j < clockInvDis.length; j++) {

				final List<String> primed = new ArrayList<String>();
				
				final String[] clockInvSplitted = clockInvDis[j].split("/\\\\");
				fillPrimedAndUnprimedLists(clockInvSplitted, primed, new ArrayList<String>());
				
				primed.addAll(primedForStateInv);
				primed.addAll(initConstraints);
				
				writeTransition("init", phase.getName(), primed, new ArrayList<String>(), varString, primedVarString);
			}
		}
	}

	protected void createTransitionNode(Transition trans, String varString,
			String primedVarString) throws IOException {
		final String source = trans.getSrc().getName();
		final String dest = trans.getDest().getName();
		//boolean sourceEqualDest = source.equals(dest);

		// //////COMPUTE CONT//////////////////////////////////////////
		//StringBuffer cont = new StringBuffer("");
		//if (sourceEqualDest) {
		//	cont.append(this.cont);
		//}

		// //////COMPUTE GUARD DISJUNCTS///////////////////////////////
		final String[] guardDis = formulaConverter.getDisjuncts(false, trans
                        .getGuard(),numberOfDNFs);

                // //////COMPUTE CLOCK EXPRESSION//////////////////////////////
                final StringBuffer clockExprBuf = new StringBuffer();
                final String[] resets = trans.getResets();
                final ArrayList<String> notReset = new ArrayList<String>(clocks);
                notReset.removeAll(Arrays.asList(resets));
                for (int i = 0; i < resets.length; i++) {
                    clockExprBuf.append(" /\\ _" + resets[i] + "' = "+
					(trans.getDest().isStopped(resets[i]) ? "0" : "_len'"));
                }
                final Iterator notResetIter = notReset.iterator();
                while (notResetIter.hasNext()) {
                        final String aktNotReset = (String) notResetIter.next();
                        clockExprBuf.append(" /\\ _" + aktNotReset + "' = _" + aktNotReset + " + " +
					    (trans.getDest().isStopped(aktNotReset) ? "0" : "_len'"));
                }
                final String clockExpr = "_len' > 0" + clockExprBuf.toString().trim();
                final String[] clockExprConj = clockExpr.split("/\\\\");
                
		// //////COMPUTE INVARIANTS EXPRESSION/////////////////////////
		final String[] invp2 = compInvariantsExpression(trans.getDest());

		// //////BUILD TRANSITIONS/////////////////////////////////////
		for (int i = 0; i < invp2.length; i++) {
			//String[] sepInvConj = invp2[i]!= null ? invp2[i].split("/\\\\") : null;

			final List<String> primedForSepInvConj = new ArrayList<String>();
			final List<String> unprimedForSepInvConj = new ArrayList<String>();

                        //Add clock expressions
                        fillPrimedAndUnprimedLists(clockExprConj, primedForSepInvConj,
                                unprimedForSepInvConj);

                        //Add invariant expressions
                        if(invp2[i] != null){
                            final String[] sepInvConj = invp2[i].split("/\\\\");
                            fillPrimedAndUnprimedLists(sepInvConj, primedForSepInvConj,
                                    unprimedForSepInvConj);
                        }
                        
			for (int j = 0; j < guardDis.length; j++) {
				final String[] sepGuardConj = guardDis[j].split("/\\\\");

				final ArrayList<String> primed = new ArrayList<String>();
				final ArrayList<String> unprimed = new ArrayList<String>();
				primed.addAll(primedForSepInvConj);
				unprimed.addAll(unprimedForSepInvConj);
				fillPrimedAndUnprimedLists(sepGuardConj, primed, unprimed);

				writeTransition(source, dest, primed, unprimed, varString,
						primedVarString);
			}
		}
	}

        
	protected String[] compInvariantsExpression(Phase phase) {
		final String[] stateInvDis = formulaConverter.getDisjuncts(true, phase.getStateInvariant(),numberOfDNFs);
		final String[] clockInvDis = formulaConverter.getDisjuncts(true, phase.getClockInvariant(),numberOfDNFs);
		final String[] invp2 = new String[stateInvDis.length * clockInvDis.length];
		for (int i = 0; i < stateInvDis.length; i++) {
			for (int j = 0; j < clockInvDis.length; j++) {
				invp2[(i * clockInvDis.length) + j] = "";
				if (!stateInvDis[i].equals("")) {
                    invp2[(i * clockInvDis.length) + j] += stateInvDis[i];
				}
				if (!clockInvDis[j].equals("")) {
                    if(invp2[(i * clockInvDis.length) + j] != "") {
						invp2[(i * clockInvDis.length) + j] += " /\\ "
                            + clockInvDis[j];
					} else {
						invp2[(i * clockInvDis.length) + j] += clockInvDis[j];
					}
				}
			}
		}

		return invp2;
	}

    /*	protected void computeCont() {
		StringBuffer result = new StringBuffer("");
		result.append("_disc < 1 /\\ _disc' = 1");
		if (!this.clocks.isEmpty()) {
			Iterator clocksIterator = this.clocks.iterator();
			while (clocksIterator.hasNext()) {
				String actClock = (String) clocksIterator.next();
				result.append(" /\\ _" + actClock + "' = _" + actClock
						+ " + _len ");
			}
		}
		Iterator varIterator = this.additionalVariables.iterator();
		while (varIterator.hasNext()) {
			String actVariable = (String) varIterator.next();
			result.append(" /\\ _" + actVariable + "' = _" + actVariable);
		}
		this.cont = result.toString();
        }*/

	protected void fillClockList() {
		clocks = new ArrayList<String>();

		final Iterator addVarIter = additionalVariables.iterator();
		final Iterator addTypesIter = additionalTypes.iterator();
		while (addVarIter.hasNext()) {
			final String actVar = (String) addVarIter.next();
			final String actType = (String) addTypesIter.next();
			if (actType.equals("Time")) {
				clocks.add(actVar);
			}
		}
	}

	protected void fillPrimedAndUnprimedLists(String[] clauses,
			List<String> primed, List<String> unprimed) {
		for (int k = 0; k < clauses.length; k++) {
			if (clauses[k].contains("'")) {
				primed.add(clauses[k].trim());
			} else if(!clauses[k].equals("")){ 
				unprimed.add(clauses[k].trim());
			}
		}
	}

	protected void writeTransition(String source, String dest, List<String> primed,
			List<String> unprimed, String varString, String primedVarString)
			throws IOException {
		writer.write("r(p(pc(" + source + "),data(" + varString + ")),");
		writer.write("p(pc(" + dest + "),data(" + primedVarString
				+ ")), [");

		final Iterator unprimedIter = unprimed.iterator();
		while (unprimedIter.hasNext()) {
			final String actClause = (String) unprimedIter.next();
			writer.write(actClause);
			if (unprimedIter.hasNext()) {
				writer.write(",");
			}
		}

		writer.write("],[");

		final Iterator primedIter = primed.iterator();
		while (primedIter.hasNext()) {
			final String actClause = (String) primedIter.next();
			writer.write(actClause.replace("'", "P"));
			if (primedIter.hasNext()) {
				writer.write(",");
			}
		}

		writer.write("]," + (transCounter++) + ").\n");
	}

    public void computeNumberOfDNFs(PhaseEventAutomata pea){
        final Phase[] phases = pea.getPhases();
        numberOfDNFs = 0;
        for (int i = 0; i < phases.length; i++) {
            numberOfDNFs += phases[i].getTransitions().size()*3;
        }
        numberOfDNFs += pea.getInit().length*2;
    }
    
//	public static void main(String[] args) {
//		try {
//			PEAXML2JConverter xml2j = new PEAXML2JConverter(false);
//			PhaseEventAutomata[] peas = xml2j
//					.convert("./pea/modelchecking/CaseStudy/Property0_par.xml");
//			peas[0].dump();
//			//PEA2ARMCConverterRevised pea2armcFast = new PEA2ARMCConverterRevised();  
//			ArrayList<String> addVars = new ArrayList<String>();
//			ArrayList<String> addTypes = new ArrayList<String>();
//			addVars.add("add1");
//			addVars.add("add2");
//			addVars.add("add3");
//			addTypes.add("Time");
//			addTypes.add("none");
//			addTypes.add("bla");
//
//			//			pea2armcFast.convert(peas[0],
//			//					"./pea/modelchecking/example/tcs3.xml", "./pea/modelchecking/example/namemapping.xml",addVars, addTypes,
//			//					true);
//		} catch (Exception e) {
//			System.out.println("Outermost exception");
//			e.printStackTrace();
//		}
//	}

}
