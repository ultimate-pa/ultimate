package de.uni_freiburg.informatik.ultimate.smtsolver.external;

import java.io.IOException;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.core.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
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

	private Term[] readInterpolants(int numberOfInterpolants) throws AssertionError {
		Term[] interpolants;
    	switch (m_ExternalInterpolator) {
		case IZ3:
		case PRINCESS:
	    	interpolants = new Term[numberOfInterpolants];
	    	for (int i=0; i<interpolants.length; i++) {
	    		interpolants[i] = super.m_Executor.parseTerm();
	    	}

			break;
		case SMTINTERPOL:
			interpolants = super.m_Executor.parseGetAssertionsResult();
			break;
		default:
			throw new AssertionError("unknown m_ExternalInterpolator");
		}
		return interpolants;
	}




}
