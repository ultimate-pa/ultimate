package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.abstractdomain;

import java.util.ArrayList;
import java.util.List;
import java.util.Set;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.preferences.AIPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.compounddomain.*;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.polytopedomain.*;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.valuedomain.*;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.valuedomain.booldomain.*;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.valuedomain.intervaldomain.*;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.valuedomain.signdomain.*;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.valuedomain.topbottomdomain.*;

/**
 * Creates domains as specified in the preferences.
 * 
 * @author GROSS-JAN
 *
 */
public class AbstractDomainFactory {
	private final Logger mLogger;
	private Set<String> mNumbersForWidening;

	public AbstractDomainFactory(Logger logger) {
		mLogger = logger;
	}

	public IAbstractDomain<?> createDomain(AIPreferences preferences,
			Set<String> numbersForWidening) {
		mNumbersForWidening = numbersForWidening;
		IAbstractDomain<?> domain;
		String domainID = preferences.getDomainID();
		if (domainID.equals(ValueDomain.getDomainID())) {
			IAbstractValueFactory<?> mIntValueFactory = createValueFactory(preferences
					.getIntFactoryID());
			IAbstractValueFactory<?> mRealMergeOperator = createValueFactory(preferences
					.getRealFactoryID());
			IAbstractValueFactory<?> mBoolValueFactory = createValueFactory(preferences
					.getBoolFactoryID());
			IAbstractValueFactory<?> mBitVectorValueFactory = createValueFactory(preferences
					.getBitVectorFactoryID());
			IAbstractValueFactory<?> mStringValueFactory = createValueFactory(preferences
					.getStringFactoryID());

			domain = new ValueDomain(mIntValueFactory, mRealMergeOperator,
					mBoolValueFactory, mBitVectorValueFactory,
					mStringValueFactory, mLogger);
		} else if (domainID.equals(PolytopeDomain.getDomainID())) {
			domain = new PolytopeDomain(mLogger);
		} else if (domainID.equals(CompoundDomain.getDomainID())) {
			List<IAbstractDomain> domains = new ArrayList<IAbstractDomain>();

			// add a value domain
			IAbstractValueFactory<?> mIntValueFactory = createValueFactory(preferences
					.getIntFactoryID());
			IAbstractValueFactory<?> mRealMergeOperator = createValueFactory(preferences
					.getRealFactoryID());
			IAbstractValueFactory<?> mBoolValueFactory = createValueFactory(preferences
					.getBoolFactoryID());
			IAbstractValueFactory<?> mBitVectorValueFactory = createValueFactory(preferences
					.getBitVectorFactoryID());
			IAbstractValueFactory<?> mStringValueFactory = createValueFactory(preferences
					.getStringFactoryID());
			domain = new ValueDomain(mIntValueFactory, mRealMergeOperator,
					mBoolValueFactory, mBitVectorValueFactory,
					mStringValueFactory, mLogger);
			domains.add(domain);

			// add a polytope domain
			domains.add(new PolytopeDomain(mLogger));

			// create refinements
			List<IRefinement> refinements = new ArrayList<IRefinement>();
			// refinements.add(new IntervalToPolytopeRefinement(mLogger));

			domain = new CompoundDomain(domains, refinements);
		} else {
			mLogger.warn(String
					.format("Unknown domain \"%s\" chosen", domainID));
			return null;
		}

		// add merge and widening operators
		createMergeOperator(preferences, domain);
		createWidendingOperator(preferences, domain);

		return domain;
	}

	/**
	 * Creates the proper merge operator and puts it to the domain.
	 * 
	 * @param preferences
	 * @param domain
	 */
	private void createMergeOperator(AIPreferences preferences,
			IAbstractDomain<?> domain) {
		String opName = preferences.getMergeOpName();

		// for value domain
		if (opName.equals(ValueMergeOperator.getOperatorID())) {
			ValueDomain valueDomain = (ValueDomain) domain;

			IValueMergeOperator<?> intMergeOperator = createValueMergeOperator(
					valueDomain.getIntValueFactory(),
					preferences.getIntMergeOpName());
			IValueMergeOperator<?> realMergeOperator = createValueMergeOperator(
					valueDomain.getRealValueFactory(),
					preferences.getRealMergeOpName());
			IValueMergeOperator<?> boolMergeOperator = createValueMergeOperator(
					valueDomain.getBoolValueFactory(),
					preferences.getBoolMergeOpName());
			IValueMergeOperator<?> bitVectorMergeOperator = createValueMergeOperator(
					valueDomain.getBitVectorValueFactory(),
					preferences.getBitVectorMergeOpName());
			IValueMergeOperator<?> stringMergeOperator = createValueMergeOperator(
					valueDomain.getStringValueFactory(),
					preferences.getStringMergeOpName());

			ValueMergeOperator mergeOperator = new ValueMergeOperator(
					intMergeOperator, realMergeOperator, boolMergeOperator,
					bitVectorMergeOperator, stringMergeOperator);

			valueDomain.setMergeOperator(mergeOperator);
		} else if (opName.equals(CompoundOperator.getOperatorID())) {
			List<IAbstractOperator> operators = new ArrayList<IAbstractOperator>();

			// add a value merge operator
			ValueDomain valueDomain = (ValueDomain) ((CompoundDomain) domain)
					.getDomain(0);

			IValueMergeOperator<?> intMergeOperator = createValueMergeOperator(
					valueDomain.getIntValueFactory(),
					preferences.getIntMergeOpName());
			IValueMergeOperator<?> realMergeOperator = createValueMergeOperator(
					valueDomain.getRealValueFactory(),
					preferences.getRealMergeOpName());
			IValueMergeOperator<?> boolMergeOperator = createValueMergeOperator(
					valueDomain.getBoolValueFactory(),
					preferences.getBoolMergeOpName());
			IValueMergeOperator<?> bitVectorMergeOperator = createValueMergeOperator(
					valueDomain.getBitVectorValueFactory(),
					preferences.getBitVectorMergeOpName());
			IValueMergeOperator<?> stringMergeOperator = createValueMergeOperator(
					valueDomain.getStringValueFactory(),
					preferences.getStringMergeOpName());

			ValueMergeOperator valueMergeOperator = new ValueMergeOperator(
					intMergeOperator, realMergeOperator, boolMergeOperator,
					bitVectorMergeOperator, stringMergeOperator);

			valueDomain.setMergeOperator(valueMergeOperator);
			operators.add(valueMergeOperator);

			// add a polytope merge operator
			PolytopeDomain polytopeDomain = (PolytopeDomain) ((CompoundDomain) domain)
					.getDomain(1);
			PolytopeMergeOperator pltMergeOperator = new PolytopeMergeOperator(
					mLogger, polytopeDomain);
			polytopeDomain.setMergeOperator(pltMergeOperator);
			operators.add(pltMergeOperator);

			// put it together
			CompoundDomain gc = (CompoundDomain) domain;
			gc.setMergeOperator(new CompoundOperator(operators));
		} else if (opName.equals(PolytopeMergeOperator.getOperatorID())) {
			PolytopeDomain polytopeDomain = (PolytopeDomain) domain;
			PolytopeMergeOperator mergeOperator = new PolytopeMergeOperator(
					mLogger, polytopeDomain);
			polytopeDomain.setMergeOperator(mergeOperator);
		} else {
			mLogger.warn(String.format("Unknown merge operator \"%s\" chosen",
					opName));
		}
	}

	/**
	 * Creates the proper widening operator and puts it to the domain.
	 * 
	 * @param preferences
	 * @param domain
	 */
	private void createWidendingOperator(AIPreferences preferences,
			IAbstractDomain<?> domain) {
		String opName = preferences.getWideningOpName();

		// for value domain
		if (opName.equals(ValueWideningOperator.getOperatorID())) {
			ValueDomain valueDomain = (ValueDomain) domain;

			IValueWideningOperator<?> intWideningOperator = createValueWideningOperator(
					valueDomain.getIntValueFactory(),
					preferences.getIntWideningOpName(), preferences);
			IValueWideningOperator<?> realWideningOperator = createValueWideningOperator(
					valueDomain.getRealValueFactory(),
					preferences.getRealWideningOpName(), preferences);
			IValueWideningOperator<?> boolWideningOperator = createValueWideningOperator(
					valueDomain.getBoolValueFactory(),
					preferences.getBoolWideningOpName(), preferences);
			IValueWideningOperator<?> bitVectorWideningOperator = createValueWideningOperator(
					valueDomain.getBitVectorValueFactory(),
					preferences.getBitVectorWideningOpName(), preferences);
			IValueWideningOperator<?> stringWideningOperator = createValueWideningOperator(
					valueDomain.getStringValueFactory(),
					preferences.getStringWideningOpName(), preferences);

			ValueWideningOperator operator = new ValueWideningOperator(
					intWideningOperator, realWideningOperator,
					boolWideningOperator, bitVectorWideningOperator,
					stringWideningOperator);

			valueDomain.setWideningOperator(operator);
		} else if (opName.equals(CompoundOperator.getOperatorID())) {
			List<IAbstractOperator> operators = new ArrayList<IAbstractOperator>();

			// add a value merge operator
			ValueDomain valueDomain = (ValueDomain) ((CompoundDomain) domain)
					.getDomain(0);

			IValueWideningOperator<?> intWideningOperator = createValueWideningOperator(
					valueDomain.getIntValueFactory(),
					preferences.getIntWideningOpName(), preferences);
			IValueWideningOperator<?> realWideningOperator = createValueWideningOperator(
					valueDomain.getRealValueFactory(),
					preferences.getRealWideningOpName(), preferences);
			IValueWideningOperator<?> boolWideningOperator = createValueWideningOperator(
					valueDomain.getBoolValueFactory(),
					preferences.getBoolWideningOpName(), preferences);
			IValueWideningOperator<?> bitVectorWideningOperator = createValueWideningOperator(
					valueDomain.getBitVectorValueFactory(),
					preferences.getBitVectorWideningOpName(), preferences);
			IValueWideningOperator<?> stringWideningOperator = createValueWideningOperator(
					valueDomain.getStringValueFactory(),
					preferences.getStringWideningOpName(), preferences);

			ValueWideningOperator vWideningOperator = new ValueWideningOperator(
					intWideningOperator, realWideningOperator,
					boolWideningOperator, bitVectorWideningOperator,
					stringWideningOperator);
			valueDomain.setWideningOperator(vWideningOperator);
			operators.add(vWideningOperator);

			// add a polytope merge operator
			PolytopeDomain polytopeDomain = (PolytopeDomain) ((CompoundDomain) domain)
					.getDomain(1);
			PolytopeWideningOperator pltWideningOperator = new PolytopeWideningOperator(
					mLogger, polytopeDomain);
			polytopeDomain.setWideningOperator(pltWideningOperator);
			operators.add(pltWideningOperator);

			// put it together
			CompoundDomain gc = (CompoundDomain) domain;
			gc.setWideningOperator(new CompoundOperator(operators));
		} else if (opName.equals(PolytopeWideningOperator.getOperatorID())) {
			PolytopeDomain polytopeDomain = (PolytopeDomain) domain;

			PolytopeWideningOperator wideningOperator = new PolytopeWideningOperator(
					mLogger, polytopeDomain);

			polytopeDomain.setWideningOperator(wideningOperator);
		} else if (opName
				.equals(PolytopeBHRZ03WideningOperator.getOperatorID())) {
			PolytopeDomain polytopeDomain = (PolytopeDomain) domain;

			PolytopeBHRZ03WideningOperator wideningOperator = new PolytopeBHRZ03WideningOperator(
					mLogger, polytopeDomain);

			polytopeDomain.setWideningOperator(wideningOperator);
		} else {
			mLogger.warn(String.format("Unknown merge operator \"%s\" chosen",
					opName));
		}
	}

	/*
	 * @param domainID
	 * 
	 * @return An abstract domain factory for the abstract domain system given
	 * by its ID
	 */
	private IAbstractValueFactory<?> createValueFactory(String valueFactoryID) {
		if (valueFactoryID.equals(BoolValueFactory.getDomainID())) {
			return new BoolValueFactory(mLogger);
		}
		if (valueFactoryID.equals(SignValueFactory.getDomainID())) {
			return new SignValueFactory(mLogger);
		}
		if (valueFactoryID.equals(IntervalValueFactory.getDomainID())) {
			return new IntervalValueFactory(mLogger);
		}
		if (valueFactoryID.equals(TopBottomValueFactory.getDomainID())) {
			return new TopBottomValueFactory(mLogger);
		}
		if (valueFactoryID.equals(IntervalValueFactory.getDomainID())) {
			return new IntervalValueFactory(mLogger);
		}

		// default: TOPBOTTOM
		if (!valueFactoryID.equals(TopBottomValueFactory.getDomainID())) {
			mLogger.warn(String
					.format("Unknown value factory system \"%s\" chosen, using \"%s\" instead",
							valueFactoryID, TopBottomValueFactory.getDomainID()));
		}
		return new TopBottomValueFactory(mLogger);
	}

	private IValueMergeOperator<?> createValueMergeOperator(
			IAbstractValueFactory<?> valueFactory, String mergeOpName) {
		if (mergeOpName.equals(SignMergeWideningOperator.getName())) {
			if (valueFactory instanceof SignValueFactory) {
				return new SignMergeWideningOperator(
						(SignValueFactory) valueFactory, mLogger);
			}
		} else if (mergeOpName.equals(BoolMergeWideningOperator.getName())) {
			if (valueFactory instanceof BoolValueFactory) {
				return new BoolMergeWideningOperator(
						(BoolValueFactory) valueFactory, mLogger);
			}
		} else if (mergeOpName.equals(TopBottomMergeWideningOperator.getName())) {
			if (valueFactory instanceof TopBottomValueFactory) {
				return new TopBottomMergeWideningOperator(
						(TopBottomValueFactory) valueFactory, mLogger);
			}
		} else if (mergeOpName.equals(IntervalUnionMergeOperator.getName())) {
			if (valueFactory instanceof IntervalValueFactory) {
				return new IntervalUnionMergeOperator(
						(IntervalValueFactory) valueFactory, mLogger);
			}
		} else {
			mLogger.warn(String.format(
					"Unknown value merge operator \"%s\" chosen", mergeOpName));
			return null;
		}

		mLogger.warn(String.format(
				"Invalid value merge operator \"%s\" chosen for \"%s\"",
				mergeOpName, valueFactory.getClass().getName()));
		return null;
	}

	// Value Widening Operator
	private IValueWideningOperator<?> createValueWideningOperator(
			IAbstractValueFactory<?> valueFactory, String wideningOpName,
			AIPreferences preferences) {
		if (wideningOpName.equals(SignMergeWideningOperator.getName())) {
			if (valueFactory instanceof SignValueFactory) {
				return new SignMergeWideningOperator(
						(SignValueFactory) valueFactory, mLogger);
			}
		} else if (wideningOpName.equals(BoolMergeWideningOperator.getName())) {
			if (valueFactory instanceof BoolValueFactory) {
				return new BoolMergeWideningOperator(
						(BoolValueFactory) valueFactory, mLogger);
			}
		} else if (wideningOpName.equals(TopBottomMergeWideningOperator
				.getName())) {
			if (valueFactory instanceof TopBottomValueFactory) {
				return new TopBottomMergeWideningOperator(
						(TopBottomValueFactory) valueFactory, mLogger);
			}
		} else if (wideningOpName.equals(IntervalIntWideningOperator.getName())) {
			if (valueFactory instanceof IntervalValueFactory) {
				return new IntervalIntWideningOperator(
						(IntervalValueFactory) valueFactory,
						mNumbersForWidening, mLogger);
			}
		} else if (wideningOpName.equals(IntervalQuickWideningOperator
				.getName())) {
			if (valueFactory instanceof IntervalValueFactory) {
				return new IntervalQuickWideningOperator(
						(IntervalValueFactory) valueFactory, mLogger);
			}
		} else if (wideningOpName.equals(IntervalSetWideningOperator.getName())) {
			if (valueFactory instanceof IntervalValueFactory) {
				return new IntervalSetWideningOperator(
						(IntervalValueFactory) valueFactory,
						mNumbersForWidening, mLogger);
			}
		} else {
			mLogger.warn(String.format(
					"Unknown value widening operator \"%s\" chosen",
					wideningOpName));
			return null;
		}

		mLogger.warn(String.format(
				"Invalid value widening operator \"%s\" chosen for \"%s\"",
				wideningOpName, valueFactory.getClass().getName()));
		return null;
	}

}
