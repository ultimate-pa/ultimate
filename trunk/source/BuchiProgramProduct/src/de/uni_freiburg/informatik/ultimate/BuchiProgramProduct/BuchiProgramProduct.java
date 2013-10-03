package de.uni_freiburg.informatik.ultimate.BuchiProgramProduct;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileInputStream;
import java.io.InputStreamReader;
import java.util.ArrayList;
import java.util.Dictionary;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Observer;

import org.apache.log4j.Logger;
import org.eclipse.core.runtime.preferences.IEclipsePreferences;
import org.eclipse.core.runtime.preferences.IScopeContext;

import de.uni_freiburg.informatik.ultimate.access.IObserver;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.IGenerator;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.ISource;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.ITool.QueryKeyword;
import de.uni_freiburg.informatik.ultimate.model.GraphType;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.model.MarkedTrace;
import de.uni_freiburg.informatik.ultimate.model.TokenMap;


/**
 * This plugin implements the product algorithm described in the Masterthesis 
 *  "Automatische Generierungvon Büchi-Programmen".
 *  
 *  
 * @author Langenfeld
 * 
 *
 */
public class BuchiProgramProduct implements IGenerator {
	
	 protected static Logger Logger = UltimateServices.getInstance().getLogger(Activator.PLUGIN_ID);

	 protected List<String> m_FileNames = new ArrayList<String>();
	 
	 private BuchiProductObserver bpo;

	@Override
	public GraphType getOutputDefinition() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public List<MarkedTrace> getMarkedTraces() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public boolean isGuiRequired() {
		// TODO Auto-generated method stub
		return false;
	}

	@Override
	public void setTokenMap(TokenMap tokenMap) {
		// TODO Auto-generated method stub
		
	}

	@Override
	public QueryKeyword getQueryKeyword() {
		return  QueryKeyword.ALL;
	}


	@Override
	public void setInputDefinition(GraphType graphType) {
		// TODO Auto-generated method stub
	}

	@Override
	public List<IObserver> getObservers() {
		ArrayList<IObserver> observers = new ArrayList<IObserver>();
		observers.add(this.bpo);
		return observers;
	}

	@Override
	public IEclipsePreferences[] getPreferences(IScopeContext cs,
			IScopeContext is) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public int init(Object params) {
		this.bpo = new BuchiProductObserver();
		return 0;
	}

	@Override
	public String getName() {
		 return Activator.PLUGIN_ID;
	}

	@Override
	public String getPluginID() {
		 return Activator.PLUGIN_ID;
	}

	@Override
	public IElement getModel() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public List<String> getDesiredToolID() {
		// TODO Auto-generated method stub
		return null;
	}
	 
	
}
