/*
 * Copyright (C) 2009-2014 University of Freiburg
 *
 * This file is part of the ULTIMATE Automata Library.
 *
 * The ULTIMATE Automata Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Automata Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Automata Library.  If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Automata Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE Automata Library grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.automata;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.preferences.PreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.services.IProgressMonitorService;
import de.uni_freiburg.informatik.ultimate.core.services.IService;
import de.uni_freiburg.informatik.ultimate.core.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.IUltimatePlugin;

public class NestedWordAutomata implements IUltimatePlugin, IService {
	
	private static final String s_PLUGIN_NAME = Activator.PLUGIN_NAME;
	private static final String s_PLUGIN_ID = Activator.PLUGIN_ID;


	private IUltimateServiceProvider mServices;
	
	/********************** Hacky shit ****************************/
	// setServices(services) contains the rest  
	private static IProgressMonitorService sProgress;
	private static NWALoggerProxy sLoggerProxy;

	public static Logger getLogger() {
		if (sLoggerProxy == null) {
			sLoggerProxy = new NWALoggerProxy();
		}
		return sLoggerProxy;
	}
	
	public static IProgressMonitorService getMonitor(){
		return sProgress;
	}
	
	
	/********************** End hacky shit ****************************/ 

	@Override
	public String getPluginName() {
		return s_PLUGIN_NAME;
	}

	@Override
	public String getPluginID() {
		return s_PLUGIN_ID;
	}

	@Override
	public UltimatePreferenceInitializer getPreferences() {
		return new PreferenceInitializer();
	}

	//@Override
	public void setToolchainStorage(IToolchainStorage storage) {
		// TODO Auto-generated method stub

	}

	//@Override
	public void setServices(IUltimateServiceProvider services) {
		mServices = services;

		// TODO: Huge hack, but real change has to be coordinated with Matthias
		sProgress = services.getProgressMonitorService();
		((NWALoggerProxy) getLogger()).setLogger(services.getLoggingService().getLogger(Activator.PLUGIN_ID));
	}

	@Override
	public void destroy() {
		// TODO Auto-generated method stub
		
	}

	public void init() {
		// TODO Auto-generated method stub
		
	}
}
