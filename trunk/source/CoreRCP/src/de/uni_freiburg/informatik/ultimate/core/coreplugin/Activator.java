/*
 * Copyright (C) 2007-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2007-2015 Robert Jakob
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE Core.
 * 
 * The ULTIMATE Core is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE Core is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Core. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Core, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE Core grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.core.coreplugin;

import org.eclipse.core.runtime.Plugin;
import org.osgi.framework.BundleContext;

/**
 * The activator class controls the plug-in life cycle.
 */
public class Activator extends Plugin {

	/**
	 * Unique Plugin ID. Similar to the one in plugin.xml
	 */
	public static final String s_PLUGIN_ID = "UltimateCore";

	/**
	 * String s_PLUGIN_NAME
	 */
	public static String s_PLUGIN_NAME = "UltimateCore";

	/**
	 * The shared instance.
	 */
	private static Activator s_Plugin;

	/**
	 * The constructor. Does nothing important.
	 */
	public Activator() {
	}

	/**
	 * Method is called when plugin is started.
	 * 
	 * @see org.eclipse.ui.plugin.AbstractUIPlugin#start(org.osgi.framework.BundleContext)
	 * @param context
	 *            The Context in which plugin is started.
	 * @throws Exception
	 *             Can throw any exception
	 */
	public final void start(final BundleContext context) throws Exception {
		super.start(context);
		s_Plugin = this;
	}

	/**
	 * Method is called when plugin is stopped.
	 * 
	 * @see org.eclipse.ui.plugin.AbstractUIPlugin#stop(org.osgi.framework.BundleContext)
	 * @param context
	 *            The Context in which plugin is stopped.
	 * @throws Exception
	 *             Can throw any exception
	 */
	public final void stop(final BundleContext context) throws Exception {
		s_Plugin = null;
		super.stop(context);
		System.out.println("Closed successfully");
	}

	/**
	 * Returns the shared instance.
	 * 
	 * @return the shared instance
	 */
	public static Activator getDefault() {
		return s_Plugin;
	}

}
