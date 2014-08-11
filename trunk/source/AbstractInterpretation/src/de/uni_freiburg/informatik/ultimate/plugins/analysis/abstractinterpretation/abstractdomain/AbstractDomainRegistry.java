/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.booldomain.BoolDomainFactory;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.booldomain.BoolMergeWideningOperator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.intervaldomain.IntervalDomainFactory;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.intervaldomain.IntervalIntWideningOperator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.intervaldomain.IntervalQuickWideningOperator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.intervaldomain.IntervalSetWideningOperator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.intervaldomain.IntervalUnionMergeOperator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.signdomain.SignDomainFactory;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.signdomain.SignMergeWideningOperator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.topbottomdomain.TopBottomDomainFactory;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.topbottomdomain.TopBottomMergeWideningOperator;

/**
 * Collects abstract domains as well as their widening and merge operators.
 * Currently, classes must be added manually; expand the initialize() method to register your classes!
 * 
 * @author Christopher Dillo
 */
public class AbstractDomainRegistry {

	/**
	 * A set of domain IDs
	 */
	private final Set<String> m_domainIDs = new HashSet<String>();
	
	/**
	 * A map of domain IDs to sets of operator names
	 */
	private Map<String, Set<String>> m_wideningOperators =
			new HashMap<String, Set<String>>();

	/**
	 * A map of domain IDs to sets of operator names
	 */
	private Map<String, Set<String>> m_mergeOperators = 
			new HashMap<String, Set<String>>();
	
	// default domain IDs
	private final String defaultDomainForInt, defaultDomainForReal, defaultDomainForBool,
			defaultDomainForBitVector, defaultDomainForString;

	public AbstractDomainRegistry() {
		// INTERVAL DOMAIN
		registerDomainFactory(IntervalDomainFactory.getDomainID());
		registerWideningOperator(IntervalDomainFactory.getDomainID(), IntervalQuickWideningOperator.getName());
		registerWideningOperator(IntervalDomainFactory.getDomainID(), IntervalIntWideningOperator.getName());
		registerWideningOperator(IntervalDomainFactory.getDomainID(), IntervalSetWideningOperator.getName());
		registerMergeOperator(IntervalDomainFactory.getDomainID(), IntervalUnionMergeOperator.getName());
		
		// SIGN DOMAIN
		registerDomainFactory(SignDomainFactory.getDomainID());
		registerWideningOperator(SignDomainFactory.getDomainID(), SignMergeWideningOperator.getName());
		registerMergeOperator(SignDomainFactory.getDomainID(), SignMergeWideningOperator.getName());
		
		// BOOL DOMAIN
		registerDomainFactory(BoolDomainFactory.getDomainID());
		registerWideningOperator(BoolDomainFactory.getDomainID(), BoolMergeWideningOperator.getName());
		registerMergeOperator(BoolDomainFactory.getDomainID(), BoolMergeWideningOperator.getName());

		// TOP-BOTTOM DOMAIN
		registerDomainFactory(TopBottomDomainFactory.getDomainID());
		registerWideningOperator(TopBottomDomainFactory.getDomainID(), TopBottomMergeWideningOperator.getName());
		registerMergeOperator(TopBottomDomainFactory.getDomainID(), TopBottomMergeWideningOperator.getName());

		// default domains if no preference is set yet
		defaultDomainForInt = IntervalDomainFactory.getDomainID();
		defaultDomainForReal = IntervalDomainFactory.getDomainID();
		defaultDomainForBool = BoolDomainFactory.getDomainID();
		defaultDomainForBitVector = TopBottomDomainFactory.getDomainID();
		defaultDomainForString = TopBottomDomainFactory.getDomainID();
	}
	
	/**
	 * Register an abstract domain system ID
	 * @param domainID The domain ID of the abstract domain system
	 * @return True if successful
	 */
	public boolean registerDomainFactory(String domainID) {		
		if (!m_domainIDs.contains(domainID)) {
			return m_domainIDs.add(domainID);
		}
		return false;
	}

	/**
	 * @return The set of registered domain IDs
	 */
	public Set<String> getDomainIDs() {
		return new HashSet<String>(m_domainIDs);
	}

	/**
	 * Register a widening operator
	 * @param domainID The domain ID of the given widening operator's abstract domain system
	 * @param name The name of the given widening operator
	 * @return True if successful
	 */
	public boolean registerWideningOperator(String domainID, String name) {
		Set<String> ops = m_wideningOperators.get(domainID);
		
		if (ops == null) {
			ops = new HashSet<String>();
			m_wideningOperators.put(domainID, ops);
		}

		if (!ops.contains(name))
			return ops.add(name);
		
		return false;
	}
	
	/**
	 * @param domainID
	 * @return The set of names of widening operators registered for the given domain ID
	 */
	public Set<String> getWideningOperators(String domainID) {
		Set<String> ops = m_wideningOperators.get(domainID);
		if (ops == null) return new HashSet<String>();
		return new HashSet<String>(ops);
	}

	/**
	 * Register a merge operator
	 * @param domainID The domain ID of the given merge operator's abstract domain system
	 * @param name The name of the given merge operator
	 * @return True if successful
	 */
	public boolean registerMergeOperator(String domainID, String name) {
		Set<String> ops = m_mergeOperators.get(domainID);
		
		if (ops == null) {
			ops = new HashSet<String>();
			m_mergeOperators.put(domainID, ops);
		}

		if (!ops.contains(name))
			return ops.add(name);
		
		return false;
	}

	/**
	 * @param domainID
	 * @return The set of names of merging operators registered for the given domain ID
	 */
	public Set<String> getMergeOperators(String domainID) {
		Set<String> ops = m_mergeOperators.get(domainID);
		if (ops == null) return new HashSet<String>();
		return new HashSet<String>(ops);
	}
	
	/**
	 * @return Default domain for int
	 */
	public String getDefaultDomainIDForInt() {
		return defaultDomainForInt;
	}
	
	/**
	 * @return Default domain for real
	 */
	public String getDefaultDomainIDForReal() {
		return defaultDomainForReal;
	}
	
	/**
	 * @return Default domain for bool
	 */
	public String getDefaultDomainIDForBool() {
		return defaultDomainForBool;
	}
	
	/**
	 * @return Default domain for BitVector
	 */
	public String getDefaultDomainIDForBitVector() {
		return defaultDomainForBitVector;
	}
	
	/**
	 * @return Default domain for String
	 */
	public String getDefaultDomainIDForString() {
		return defaultDomainForString;
	}
}
