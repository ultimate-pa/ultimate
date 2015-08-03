/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.abstractdomain;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import javax.management.RuntimeErrorException;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.preferences.AIPreferences;
import de.uni_freiburg.informatik.ultimate.boogie.symboltable.BoogieSymbolTable;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.abstractdomain.booldomain.*;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.abstractdomain.intervaldomain.*;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.abstractdomain.signdomain.*;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.abstractdomain.topbottomdomain.*;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.valuedomain.*;

/**
 * Collects abstract domains as well as their widening and merge operators.
 * Currently, classes must be added manually; expand the initialize() method to
 * register your classes!
 * 
 * @author Christopher Dillo
 */
public class AbstractDomainRegistry
{
	private final Logger mLogger;

	/**
	 * A set of domain IDs
	 */
	private final Set<String> mDomainIDs = new HashSet<String>();

	/**
	 * A map of domain IDs to sets of operator names
	 */
	private Map<String, Set<String>> mWideningOperators = new HashMap<String, Set<String>>();

	/**
	 * A map of domain IDs to sets of operator names
	 */
	private Map<String, Set<String>> mMergeOperators = new HashMap<String, Set<String>>();

	
	/**
	 * A set of domain IDs
	 */
	private final Set<String> mValueFactoryIDs = new HashSet<String>();

	/**
	 * A map of domain IDs to sets of operator names
	 */
	private Map<String, Set<String>> mValueWideningOperators = new HashMap<String, Set<String>>();

	/**
	 * A map of domain IDs to sets of operator names
	 */
	private Map<String, Set<String>> mValueMergeOperators = new HashMap<String, Set<String>>();

	// default domain IDs
	private final String defaultDomain;
	private final String 		
		defaultFactoryForInt, 
		defaultFactoryForReal,
		defaultFactoryForBool,
		defaultFactoryForBitVector,
		defaultFactoryForString;


	// ---------- Constructor ------------- // 
	
	/**
	 * Constructor
	 * 
	 * @param logger
	 */
	public AbstractDomainRegistry(Logger logger)
	{
		mLogger = logger;

		// VALUE DOMAIN
		registerDomain(ValueDomain.getDomainID());

		registerOperator(mMergeOperators,
				ValueDomain.getDomainID(),
				ValueMergeOperator.getOperatorID());
		registerOperator(mWideningOperators,
				ValueDomain.getDomainID(),
				ValueWideningOperator.getOperatorID());
		
		
		// POLYTOPE DOMAIN
		// TODO: ...
	
		defaultDomain = ValueDomain.getDomainID();

		// INTERVAL FACTORY
		registerValueFactory(IntervalValueFactory.getDomainID());
		registerOperator(mValueWideningOperators,
				IntervalValueFactory.getDomainID(),
				IntervalQuickWideningOperator.getName());
		registerOperator(mValueWideningOperators,
				IntervalValueFactory.getDomainID(),
				IntervalIntWideningOperator.getName());
		registerOperator(mValueWideningOperators,
				IntervalValueFactory.getDomainID(),
				IntervalSetWideningOperator.getName());
		registerOperator(mValueMergeOperators,
				IntervalValueFactory.getDomainID(),
				IntervalUnionMergeOperator.getName());

		// SIGN FACTORY
		registerValueFactory(SignValueFactory.getDomainID());
		registerOperator(mValueWideningOperators,
				SignValueFactory.getDomainID(),
				SignMergeWideningOperator.getName());
		registerOperator(mValueMergeOperators, SignValueFactory.getDomainID(),
				SignMergeWideningOperator.getName());

		// BOOL FACTORY
		registerValueFactory(BoolValueFactory.getDomainID());
		registerOperator(mValueWideningOperators,
				BoolValueFactory.getDomainID(),
				BoolMergeWideningOperator.getName());
		registerOperator(mValueMergeOperators, BoolValueFactory.getDomainID(),
				BoolMergeWideningOperator.getName());

		// TOP-BOTTOM FACTORY
		registerValueFactory(TopBottomValueFactory.getDomainID());
		registerOperator(mValueWideningOperators,
				TopBottomValueFactory.getDomainID(),
				TopBottomMergeWideningOperator.getName());
		registerOperator(mValueMergeOperators,
				TopBottomValueFactory.getDomainID(),
				TopBottomMergeWideningOperator.getName());

		// default domains if no preference is set yet
		defaultFactoryForInt = IntervalValueFactory.getDomainID();
		defaultFactoryForReal = IntervalValueFactory.getDomainID();
		defaultFactoryForBool = BoolValueFactory.getDomainID();
		defaultFactoryForBitVector = TopBottomValueFactory.getDomainID();
		defaultFactoryForString = TopBottomValueFactory.getDomainID();
	}

	// ---------- Helper Functions ---------- //

	/**
	 * Register an abstract domain system ID.
	 * 
	 * @param domainID
	 *            The domain ID of the abstract domain system
	 * @return True if successful
	 */
	private boolean registerDomain(String domainID)
	{
		if (!mDomainIDs.contains(domainID))
		{
			return mDomainIDs.add(domainID);
		}
		return false;
	}

	/**
	 * Register an abstract value factory ID.
	 * 
	 * @param domainID
	 *            The domain ID of the abstract domain system
	 * @return True if successful
	 */
	private boolean registerValueFactory(String valueDomainID)
	{
		if (!mValueFactoryIDs.contains(valueDomainID))
		{
			return mValueFactoryIDs.add(valueDomainID);
		}
		return false;
	}

	/**
	 * Registers an operator
	 * 
	 * @param operators
	 *            The map containing the other operator instances
	 * @param domainID
	 *            The domain ID of the given merge operator's abstract domain
	 *            system
	 * @param name
	 *            The name of the given merge operator
	 * @return True if successful
	 */
	private boolean registerOperator(Map<String, Set<String>> operators,
			String valueDomainID, String name)
	{
		Set<String> ops = operators.get(valueDomainID);

		if (ops == null)
		{
			ops = new HashSet<String>();
			operators.put(valueDomainID, ops);
		}

		if (!ops.contains(name))
		{
			return ops.add(name);
		}
		return false;
	}

	// ---------- Domains ---------- //
	
	/**
	 * @return The set of registered domain IDs
	 */
	public Set<String> getDomainIDs()
	{
		return new HashSet<String>(mDomainIDs);
	}

	public int getNofDomains()
	{
		return mDomainIDs.size();
	}

	// ---------- Domain Operations ---------- //
	/** 
 	 * @param domainID
	 * @return The set of names of widening operators registered for the given
	 *         domain ID
	 */
	public Set<String> getWideningOperators(String domainID)
	{
		Set<String> ops = mWideningOperators.get(domainID);
		if (ops == null)
			return new HashSet<String>();
		return new HashSet<String>(ops);
	}

	/**
	 * @param domainID
	 * @return The set of names of merging operators registered for the given
	 *         domain ID
	 */
	public Set<String> getMergeOperators(String domainID)
	{
		Set<String> ops = mMergeOperators.get(domainID);
		if (ops == null)
		{
			return new HashSet<String>();
		}
		return new HashSet<String>(ops);
	}
	// ---------- Value Factories ---------- //
	
	/**
	 * @return The set of registered value factories IDs
	 */
	public Set<String> getValueFactoriyIDs()
	{
		return new HashSet<String>(mValueFactoryIDs);
	}
	
	public int getNofFactories()
	{
		return mValueFactoryIDs.size();
	}

	// ---------- Value Operations ---------- //
	
	/**
	 * @param domainID
	 * @return The set of names of widening operators registered for the given
	 *         domain ID
	 */
	public Set<String> getValueWideningOperators(String domainID)
	{
		Set<String> ops = mValueWideningOperators.get(domainID);
		if (ops == null)
			return new HashSet<String>();
		return new HashSet<String>(ops);
	}

	/**
	 * @param domainID
	 * @return The set of names of merging operators registered for the given
	 *         domain ID
	 */
	public Set<String> getValueMergeOperators(String domainID)
	{
		Set<String> ops = mValueMergeOperators.get(domainID);
		if (ops == null)
		{
			return new HashSet<String>();
		}
		return new HashSet<String>(ops);
	}

	// ---------- Defaults ---------- //
	
	/**
	 * @return Default domain for int
	 */
	public String getDefaultDomainID()
	{
		return defaultDomain;		
	}
	
	/**
	 * @return Default domain for int
	 */
	public String getDefaultFactoryIDForInt()
	{
		return defaultFactoryForInt;		
	}

	/**
	 * @return Default domain for real
	 */
	public String getDefaultFactoryIDForReal()
	{
		return defaultFactoryForReal;
	}

	/**
	 * @return Default domain for bool
	 */
	public String getDefaultFactoryIDForBool()
	{
		return defaultFactoryForBool;
	}

	/**
	 * @return Default domain for BitVector
	 */
	public String getDefaultFactoryIDForBitVector()
	{
		return defaultFactoryForBitVector;
	}

	/**
	 * @return Default domain for String
	 */
	public String getDefaultFactoryIDForString()
	{
		return defaultFactoryForString;
	}
}
