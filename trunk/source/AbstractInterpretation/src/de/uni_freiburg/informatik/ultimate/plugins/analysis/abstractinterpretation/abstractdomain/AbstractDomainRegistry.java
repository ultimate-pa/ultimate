/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain;

import java.util.HashMap;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.booldomain.BoolDomainFactory;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.booldomain.BoolMergeWideningOperator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.signdomain.SignDomainFactory;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.signdomain.SignMergeWideningOperator;

/**
 * Collects abstract domains as well as their widening and merge operators.
 * Currently, classes must be added manually; expand the initialize() method to register your classes!
 * 
 * @author Christopher Dillo
 */
public class AbstractDomainRegistry {

	/**
	 * A map of domain IDs to factory classes
	 */
	private static Map<String, Class<? extends IAbstractDomainFactory>> m_domainFactories =
			new HashMap<String, Class<? extends IAbstractDomainFactory>>();
	
	/**
	 * A map of domain IDs to maps of operator names to widening operator classes
	 */
	private static Map<String, Map<String, Class<? extends IWideningOperator>>> m_wideningOperators =
			new HashMap<String, Map<String, Class<? extends IWideningOperator>>>();

	/**
	 * A map of domain IDs to maps of operator names to merge operator classes
	 */
	private static Map<String, Map<String, Class<? extends IMergeOperator>>> m_mergeOperators = 
			new HashMap<String, Map<String, Class<? extends IMergeOperator>>>();
	
	private static boolean s_initialized = false;
	
	/**
	 * Initialize the registry and generate lists of registered classes.
	 * <br> Expand this method to register new classes!
	 * @return False if the registry is already initialized.
	 */
	public static boolean initialize() {
		if (s_initialized) return false;
		
		// BOOL DOMAIN
		registerDomainFactory(BoolDomainFactory.class);
		registerWideningOperator(BoolMergeWideningOperator.class);
		registerMergeOperator(BoolMergeWideningOperator.class);
		
		// SIGN DOMAIN
		registerDomainFactory(SignDomainFactory.class);
		registerWideningOperator(SignMergeWideningOperator.class);
		registerMergeOperator(SignMergeWideningOperator.class);
		
		return s_initialized = true;
	}
	
	/**
	 * Register a domain factory class
	 * @param factoryClass The class to register
	 * @return True if successful
	 */
	public static boolean registerDomainFactory(Class<? extends IAbstractDomainFactory> factoryClass) {		
		IAbstractDomainFactory factory;
		try {
			factory = factoryClass.newInstance();
		} catch (InstantiationException | IllegalAccessException e) {
			e.printStackTrace();
			return false;
		}
		
		if (!m_domainFactories.containsKey(factory.getDomainID())) {
			return m_domainFactories.put(factory.getDomainID(), factoryClass) != null;
		}
		
		return false;
	}

	/**
	 * @return The map ID->Class of registered domain factories
	 */
	public static Map<String, Class<? extends IAbstractDomainFactory>> getDomainFactories() {
		return m_domainFactories;
	}

	/**
	 * @param domainID
	 * @return The abstract domain factory for the given domain ID
	 */
	public static Class<? extends IAbstractDomainFactory> getDomainFactory(String domainID) {
		return m_domainFactories.get(domainID);
	}

	/**
	 * Register a widening operator class
	 * @param wideningOperatorClass The class to register
	 * @return True if successful
	 */
	public static boolean registerWideningOperator(Class<? extends IWideningOperator> wideningOperatorClass) {
		IWideningOperator op;
		try {
			op = wideningOperatorClass.newInstance();
		} catch (InstantiationException | IllegalAccessException e) {
			e.printStackTrace();
			return false;
		}
		
		Map<String, Class<? extends IWideningOperator>> opList = getWideningOperators(op.getDomainID());
		
		if (opList == null) {
			opList = new HashMap<String, Class<? extends IWideningOperator>>();
			m_wideningOperators.put(op.getDomainID(), opList);
		}

		if (!opList.containsKey(op.getName()))
			return opList.put(op.getName(), wideningOperatorClass) != null;
		
		return false;
	}
	
	/**
	 * @param domainID
	 * @return The map Name->Class of widening operators registered for the given domain ID
	 */
	public static Map<String, Class<? extends IWideningOperator>> getWideningOperators(String domainID) {
		return m_wideningOperators.get(domainID);
	}
	
	/**
	 * @param domainID
	 * @param operatorName
	 * @return The widening operator with the given name for the given domain ID, null if it does not exist
	 */
	public static Class<? extends IWideningOperator> getWideningOperator(String domainID, String operatorName) {
		Map<String, Class<? extends IWideningOperator>> opList = getWideningOperators(domainID);
		
		if (opList == null) return null;
		
		return opList.get(operatorName);
	}

	/**
	 * Register a merge operator class
	 * @param mergeOperatorClass The class to register
	 * @return True if successful
	 */
	public static boolean registerMergeOperator(Class<? extends IMergeOperator> mergeOperatorClass) {
		IMergeOperator op;
		try {
			op = mergeOperatorClass.newInstance();
		} catch (InstantiationException | IllegalAccessException e) {
			e.printStackTrace();
			return false;
		}
		
		Map<String, Class<? extends IMergeOperator>> opList = getMergeOperators(op.getDomainID());
		
		if (opList == null) {
			opList = new HashMap<String, Class<? extends IMergeOperator>>();
			m_mergeOperators.put(op.getDomainID(), opList);
		}

		if (!opList.containsKey(op.getName()))
			return opList.put(op.getName(), mergeOperatorClass) != null;
		
		return false;
	}

	/**
	 * @param domainID
	 * @return The map Name->Class of merging operators registered for the given domain ID
	 */
	public static Map<String, Class<? extends IMergeOperator>> getMergeOperators(String domainID) {
		return m_mergeOperators.get(domainID);
	}
	
	/**
	 * @param domainID
	 * @param operatorName
	 * @return The merge operator with the given name for the given domain ID, null if it does not exist
	 */
	public static Class<? extends IMergeOperator> getMergeOperator(String domainID, String operatorName) {
		Map<String, Class<? extends IMergeOperator>> opList = getMergeOperators(domainID);
		
		if (opList == null) return null;
		
		return opList.get(operatorName);
	}
}
