package reqCheck;

/**
 * The class <code>Consistent</code> offers functionality to
 * check whether a Phase Event automaton contains an infinite run. Thus a requirements set represented in a PEA
 * can be checked for consistency: i.e., a requirements set is consistent if A is not empty and contains at least 
 * 1 infinite run.
 * Note that this check is only semicorrect!!
 * if it returns true, then the requirements set is in fact consistent
 * if it returns false, then the requirements set may be inconsistent OR nevertheless consistent! 
 * There are examples such that every location contains a clockInvariant, but the automaton nevertheless contains an
 * infinite run. 
 * 
 * @author Amalinda Oertel
 * August 2010
 * 
 * @see pea.CDD
 */

import java.lang.management.ManagementFactory;
import java.lang.management.ThreadMXBean;

import pea.CDD;
import pea.Phase;
import pea.PhaseEventAutomata;

public class Consistent {
	
	public long getCpuTime( ) {		
	    ThreadMXBean bean = ManagementFactory.getThreadMXBean( );
	    return bean.isCurrentThreadCpuTimeSupported( ) ?
	        bean.getCurrentThreadCpuTime( ) : 0L;
	}
	
	public boolean checkConsistency(PhaseEventAutomata pea){
		int numberOfLocations = pea.getNumberOfLocations();
		for(int i=0; i< numberOfLocations; i++){
			Phase location = pea.getPhases()[i];
			if (location.getClockInvariant() == CDD.TRUE){
				
				return true;
			}
		}
		return false;
	}

}
