package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.core.runtime.Plugin;
import org.osgi.framework.BundleContext;

import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IAbstractDomainFactory;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IMergeOperator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.IWideningOperator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.signdomain.SignDomainFactory;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.signdomain.SignMergeWidenOperator;

/**
 * The activator class controls the plug-in life cycle
 */
public class Activator extends Plugin {

	// The plug-in ID
	public static final String s_PLUGIN_ID = "AbstractInterpretation";

	// The plug-in name
	public static final String s_PLUGIN_NAME = "AbstractInterpretation";
	
	// The shared instance
	private static Activator m_Plugin;

	// lists to collect classes for the abstract domain system modules
	private static final List<Class<? extends IAbstractDomainFactory>> m_domainFactories =
			new ArrayList<Class<? extends IAbstractDomainFactory>>();
	// TODO: Map AbstractDomainID to List<IWideningOperator>
	private static final List<Class<? extends IWideningOperator>> m_wideningOperators =
			new ArrayList<Class<? extends IWideningOperator>>();
	// TODO: Map AbstractDomainID to List<IMergeOperator>
	private static final List<Class<? extends IMergeOperator>> m_mergeOperators =
			new ArrayList<Class<? extends IMergeOperator>>();
	
	/**
	 * The constructor
	 */
	public Activator() {
		
		// TODO: init: collect classes... somehow.
		m_domainFactories.add(SignDomainFactory.class);
		m_wideningOperators.add(SignMergeWidenOperator.class);
		m_mergeOperators.add(SignMergeWidenOperator.class);
	}

	/*
	 * (non-Javadoc)
	 * @see org.eclipse.ui.plugin.AbstractUIPlugin#start(org.osgi.framework.BundleContext)
	 */
	public void start(BundleContext context) throws Exception {
		super.start(context);
		m_Plugin = this;
	}

	/*
	 * (non-Javadoc)
	 * @see org.eclipse.ui.plugin.AbstractUIPlugin#stop(org.osgi.framework.BundleContext)
	 */
	public void stop(BundleContext context) throws Exception {
		m_Plugin = null;
		super.stop(context);
	}

	/**
	 * Returns the shared instance
	 *
	 * @return the shared instance
	 */
	public static Activator getDefault() {
		return m_Plugin;
	}

	/**
	 * @return A list of all classes implementing IAbstractDomainFactory found in the abstractdomain package
	 */
	public static List<Class<? extends IAbstractDomainFactory>> getDomainFactories() {
		return m_domainFactories;
	}

	/**
	 * @return A list of all classes implementing IWideningOperator found in the abstractdomain package
	 */
	public static List<Class<? extends IWideningOperator>> getWideningOperators() {
		return m_wideningOperators;
	}

	/**
	 * @return A list of all classes implementing IMergeOperator found in the abstractdomain package
	 */
	public static List<Class<? extends IMergeOperator>> getMergeOperators() {
		return m_mergeOperators;
	}

	/**
	 * @return A list of all classes implementing IWideningOperator found in the abstractdomain package
	 * which belong to the abstract domain system given by the domainID 
	 */
	public static List<Class<? extends IWideningOperator>> getWideningOperators(String domainID) {
		ArrayList<Class<? extends IWideningOperator>> result =
				new ArrayList<Class<? extends IWideningOperator>>();
		for (Class<? extends IWideningOperator> c : m_wideningOperators) {
			try {
				if (c.newInstance().getDomainID().equals(domainID))
					result.add(c);
			} catch (Exception e) {
				e.printStackTrace();
			}
		}
		return result;
	}

	/**
	 * @return A list of all classes implementing IMergeOperator found in the abstractdomain package
	 * which belong to the abstract domain system given by the domainID 
	 */
	public static List<Class<? extends IMergeOperator>> getMergeOperators(String domainID) {
		ArrayList<Class<? extends IMergeOperator>> result =
				new ArrayList<Class<? extends IMergeOperator>>();
		for (Class<? extends IMergeOperator> c : m_mergeOperators) {
			try {
				if (c.newInstance().getDomainID().equals(domainID))
					result.add(c);
			} catch (Exception e) {
				e.printStackTrace();
			}
		}
		return result;
	}
}
