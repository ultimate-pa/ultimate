package de.uni_freiburg.informatik.ultimate.plugins.generator.rankingfunctions;


/**
 * A superclass for all classes that need to keep track of their instance number
 * 
 * Various routines of the RankingFunction package generate SMTLib variables.
 * In order to make sure that the same variables are generated only once, each
 * generated variable will be annotated with the respective instance number.
 * 
 * @author Jan Leike
 */
public class InstanceCounting {
	
	/**
	 *  Global instance counter
	 */
	private static long s_instance_counter = 0;
	
	/**
	 *  Number of the current instance
	 */
	protected final long m_instance;
	
	public InstanceCounting() {
		/*
		 * This assertion is violated if ultimate runs for so long that the
		 * counter overflows.
		 */
		assert(s_instance_counter >= 0);
		
		m_instance = s_instance_counter;
		s_instance_counter++;
	}
}
