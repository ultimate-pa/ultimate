/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain;

import java.util.HashMap;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.booldomain.BoolDomainFactory;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.booldomain.BoolMergeWideningOperator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.intervaldomain.IntervalDomainFactory;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.intervaldomain.IntervalQuickWideningOperator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.intervaldomain.IntervalUnionMergeOperator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.signdomain.SignDomainFactory;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.signdomain.SignMergeWideningOperator;

/**
 * Collects abstract domains as well as their widening and merge operators.
 * Currently, classes must be added manually; expand the initialize() method to register your classes!
 * 
 * @author Christopher Dillo
 */
public class AbstractDomainRegistry {
	
	private static AbstractDomainRegistry s_instance;

	/**
	 * A map of domain IDs to factory classes
	 */
	private Map<String, Class<? extends IAbstractDomainFactory<?>>> m_domainFactories =
			new HashMap<String, Class<? extends IAbstractDomainFactory<?>>>();
	
	/**
	 * A map of domain IDs to maps of operator names to widening operator classes
	 */
	private Map<String, Map<String, Class<? extends IWideningOperator<?>>>> m_wideningOperators =
			new HashMap<String, Map<String, Class<? extends IWideningOperator<?>>>>();

	/**
	 * A map of domain IDs to maps of operator names to merge operator classes
	 */
	private Map<String, Map<String, Class<? extends IMergeOperator<?>>>> m_mergeOperators = 
			new HashMap<String, Map<String, Class<? extends IMergeOperator<?>>>>();

	private AbstractDomainRegistry() {
		// INTERVAL DOMAIN
		registerDomainFactory(IntervalDomainFactory.getDomainID(), IntervalDomainFactory.class);
		registerWideningOperator(IntervalDomainFactory.getDomainID(), IntervalQuickWideningOperator.getName(), IntervalQuickWideningOperator.class);
		registerMergeOperator(IntervalDomainFactory.getDomainID(), IntervalUnionMergeOperator.getName(), IntervalUnionMergeOperator.class);
		
		// SIGN DOMAIN
		registerDomainFactory(SignDomainFactory.getDomainID(), SignDomainFactory.class);
		registerWideningOperator(SignDomainFactory.getDomainID(), SignMergeWideningOperator.getName(), SignMergeWideningOperator.class);
		registerMergeOperator(SignDomainFactory.getDomainID(), SignMergeWideningOperator.getName(), SignMergeWideningOperator.class);
	}

	/**
	 * @return the singleton object...
	 */
	public static AbstractDomainRegistry getInstance() {
		if (s_instance == null)
			s_instance = new AbstractDomainRegistry();
		
		return s_instance;
	}
	
	/**
	 * Register a domain factory class
	 * @param domainID The domain ID of the given factory's abstract domain system
	 * @param factoryClass The class to register
	 * @return True if successful
	 */
	public boolean registerDomainFactory(String domainID, Class<? extends IAbstractDomainFactory<?>> factoryClass) {		
		if (!m_domainFactories.containsKey(domainID)) {
			return m_domainFactories.put(domainID, factoryClass) != null;
		}
		return false;
	}

	/**
	 * @return The map ID->Class of registered domain factories
	 */
	public Map<String, Class<? extends IAbstractDomainFactory<?>>> getDomainFactories() {
		return m_domainFactories;
	}

	/**
	 * @param domainID
	 * @return The abstract domain factory for the given domain ID
	 */
	public Class<? extends IAbstractDomainFactory<?>> getDomainFactory(String domainID) {
		return m_domainFactories.get(domainID);
	}

	/**
	 * Register a widening operator class
	 * @param domainID The domain ID of the given widening operator's abstract domain system
	 * @param name The name of the given widening operator
	 * @param wideningOperatorClass The class to register
	 * @return True if successful
	 */
	public boolean registerWideningOperator(String domainID, String name, Class<? extends IWideningOperator<?>> wideningOperatorClass) {
		Map<String, Class<? extends IWideningOperator<?>>> opList = getWideningOperators(domainID);
		
		if (opList == null) {
			opList = new HashMap<String, Class<? extends IWideningOperator<?>>>();
			m_wideningOperators.put(domainID, opList);
		}

		if (!opList.containsKey(name))
			return opList.put(name, wideningOperatorClass) != null;
		
		return false;
	}
	
	/**
	 * @param domainID
	 * @return The map Name->Class of widening operators registered for the given domain ID
	 */
	public Map<String, Class<? extends IWideningOperator<?>>> getWideningOperators(String domainID) {
		return m_wideningOperators.get(domainID);
	}
	
	/**
	 * @param domainID
	 * @param operatorName
	 * @return The widening operator with the given name for the given domain ID, null if it does not exist
	 */
	public Class<? extends IWideningOperator<?>> getWideningOperator(String domainID, String operatorName) {
		Map<String, Class<? extends IWideningOperator<?>>> opList = getWideningOperators(domainID);
		
		if (opList == null) return null;
		
		return opList.get(operatorName);
	}

	/**
	 * Register a merge operator class
	 * @param domainID The domain ID of the given merge operator's abstract domain system
	 * @param name The name of the given merge operator
	 * @param mergeOperatorClass The class to register
	 * @return True if successful
	 */
	public boolean registerMergeOperator(String domainID, String name, Class<? extends IMergeOperator<?>> mergeOperatorClass) {
		Map<String, Class<? extends IMergeOperator<?>>> opList = getMergeOperators(domainID);
		
		if (opList == null) {
			opList = new HashMap<String, Class<? extends IMergeOperator<?>>>();
			m_mergeOperators.put(domainID, opList);
		}

		if (!opList.containsKey(name))
			return opList.put(name, mergeOperatorClass) != null;
		
		return false;
	}

	/**
	 * @param domainID
	 * @return The map Name->Class of merging operators registered for the given domain ID
	 */
	public Map<String, Class<? extends IMergeOperator<?>>> getMergeOperators(String domainID) {
		return m_mergeOperators.get(domainID);
	}
	
	/**
	 * @param domainID
	 * @param operatorName
	 * @return The merge operator with the given name for the given domain ID, null if it does not exist
	 */
	public Class<? extends IMergeOperator<?>> getMergeOperator(String domainID, String operatorName) {
		Map<String, Class<? extends IMergeOperator<?>>> opList = getMergeOperators(domainID);
		
		if (opList == null) return null;
		
		return opList.get(operatorName);
	}
}
