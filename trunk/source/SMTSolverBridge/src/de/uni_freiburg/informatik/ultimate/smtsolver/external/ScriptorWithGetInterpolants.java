/*
 * Copyright (C) 2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE SMTSolverBridge.
 * 
 * The ULTIMATE SMTSolverBridge is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE SMTSolverBridge is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE SMTSolverBridge. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE SMTSolverBridge, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE SMTSolverBridge grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.smtsolver.external;

import java.io.IOException;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.core.services.model.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.services.model.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.PrintTerm;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 * Subclass of Scriptor that has support for the not yet standardized
 * get-interpolants command.
 * Supports iZ3 and Princess.
 * @author Matthias Heizmann
 *
 */
public class ScriptorWithGetInterpolants extends Scriptor {
	
	public enum ExternalInterpolator { IZ3, PRINCESS, SMTINTERPOL };
	
	private final ExternalInterpolator m_ExternalInterpolator;

	public ScriptorWithGetInterpolants(String command, Logger logger,
			IUltimateServiceProvider services, IToolchainStorage storage, 
			ExternalInterpolator externalInterpolator)
			throws IOException {
		super(command, logger, services, storage);
		m_ExternalInterpolator = externalInterpolator;
	}

    @Override
    public Term[] getInterpolants(Term[] partition) throws SMTLIBException,
    											UnsupportedOperationException {
    	sendInterpolationCommand(partition);
    	
    	Term[] interpolants = readInterpolants(partition.length - 1);
    	return interpolants;
    }
    
    @Override
    public Term[] getInterpolants(Term[] partition, int[] startOfSubtree) throws SMTLIBException,
    											UnsupportedOperationException {
    	sendInterpolationCommand(partition, startOfSubtree);
    	
    	Term[] interpolants = readInterpolants(partition.length - 1);
    	return interpolants;
    }
    
	private void sendInterpolationCommand(Term[] partition)
			throws AssertionError {
		StringBuilder command = new StringBuilder();
    	PrintTerm pt = new PrintTerm();
    	switch (m_ExternalInterpolator) {
		case IZ3:
			command.append("(get-interpolant ");
			break;
		case PRINCESS:
		case SMTINTERPOL:
			command.append("(get-interpolants ");
			break;
		default:
			throw new AssertionError("unknown m_ExternalInterpolator");
		}
    	String sep = "";
    	for (Term t : partition) {
    		command.append(sep);
    		pt.append(command, t);
    		sep = " ";
    	}
    	command.append(")");
    	super.m_Executor.input(command.toString());
	}
	
	
	
	private void sendInterpolationCommand(Term[] partition, int[] startOfSubtree)
			throws AssertionError {
		StringBuilder command = new StringBuilder();
    	PrintTerm pt = new PrintTerm();
    	switch (m_ExternalInterpolator) {
		case IZ3:
			command.append("(get-interpolant ");
			break;
		case PRINCESS:
		case SMTINTERPOL:
			command.append("(get-interpolants ");
			break;
		default:
			throw new AssertionError("unknown m_ExternalInterpolator");
		}
    	pt.append(command, partition[0]);
    	for (int i = 1; i < partition.length; ++i) {
    		int prevStart = startOfSubtree[i - 1];
    		while (startOfSubtree[i] < prevStart) {
    			command.append(')');
    			prevStart = startOfSubtree[prevStart - 1];
    		}
    		command.append(' ');
    		if (startOfSubtree[i] == i)
    			command.append('(');
    		pt.append(command, partition[i]);
    	}
    	command.append(')');
    	super.m_Executor.input(command.toString());
	}
	


	private Term[] readInterpolants(int numberOfInterpolants) throws AssertionError {
		Term[] interpolants;
    	switch (m_ExternalInterpolator) {
		case IZ3:
	    	interpolants = new Term[numberOfInterpolants];
	    	for (int i=0; i<interpolants.length; i++) {
	    		interpolants[i] = super.m_Executor.parseTerm();
	    	}
			break;
		case PRINCESS:
		case SMTINTERPOL:
			interpolants = super.m_Executor.parseGetAssertionsResult();
			break;
		default:
			throw new AssertionError("unknown m_ExternalInterpolator");
		}
		return interpolants;
	}




}
