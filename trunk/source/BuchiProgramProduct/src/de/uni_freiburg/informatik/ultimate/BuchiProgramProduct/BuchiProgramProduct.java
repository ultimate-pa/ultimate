package de.uni_freiburg.informatik.ultimate.BuchiProgramProduct;

import java.util.ArrayList;
import java.util.List;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.access.IObserver;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.IGenerator;
import de.uni_freiburg.informatik.ultimate.model.GraphType;
import de.uni_freiburg.informatik.ultimate.model.IElement;


/**
 * This plugin implements the product algorithm described in the Masterthesis 
 *  "Automatische Generierungvon Buchi-Programmen".
 *  
 *  
 * @author Langenfeld
 * 
 *
 */
public class BuchiProgramProduct implements IGenerator {
	
	 protected static Logger Logger = UltimateServices.getInstance().getLogger(Activator.PLUGIN_ID);

	 protected List<String> m_FileNames = new ArrayList<String>();
	 
	 private BuchiProductObserver buchiProductObserver;

	@Override
	public GraphType getOutputDefinition() {
		List<String> filenames = new ArrayList<String>();
		filenames.add("Product");
		
		return new GraphType(Activator.PLUGIN_ID, GraphType.Type.OTHER, filenames);
	}



	@Override
	public boolean isGuiRequired() {
		// TODO Auto-generated method stub
		return false;
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
		observers.add(this.buchiProductObserver);
		return observers;
	}



	@Override
	public int init(Object params) {
		this.buchiProductObserver = new BuchiProductObserver();
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
		if (this.buchiProductObserver.product != null)
			return this.buchiProductObserver.product.getRCFG();
		else 
			return null;
	}

	@Override
	public List<String> getDesiredToolID() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public UltimatePreferenceInitializer getPreferences() {
		// TODO Auto-generated method stub
		return null;
	}
	 
	
}
