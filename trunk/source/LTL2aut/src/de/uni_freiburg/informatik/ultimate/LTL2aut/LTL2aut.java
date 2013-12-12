package de.uni_freiburg.informatik.ultimate.LTL2aut;

import java.util.ArrayList;
import java.util.List;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.LTL2aut.preferences.PreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.access.IObserver;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.IGenerator;
import de.uni_freiburg.informatik.ultimate.model.GraphType;
import de.uni_freiburg.informatik.ultimate.model.IElement;

public class LTL2aut implements IGenerator {
	
	 protected static Logger Logger = UltimateServices.getInstance().getLogger(Activator.PLUGIN_ID);

	 protected List<String> m_FileNames = new ArrayList<String>();
	 
	 private DummyLTL2autObserver obs;
	 
	@Override
	public int init(Object params) {
		this.obs = new DummyLTL2autObserver(); 
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
	public GraphType getOutputDefinition() {
		List<String> filenames = new ArrayList<String>();
		filenames.add("Hardcoded");
		
		return new GraphType(Activator.PLUGIN_ID, GraphType.Type.AST, filenames);
	}

	@Override
	public boolean isGuiRequired() {
		// TODO Auto-generated method stub
		return false;
	}

	@Override
	public QueryKeyword getQueryKeyword() {
		return QueryKeyword.LAST;
	}

	@Override
	public List<String> getDesiredToolID() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public void setInputDefinition(GraphType graphType) {
		// TODO Auto-generated method stub
		
	}

	@Override
	public List<IObserver> getObservers() {
		ArrayList<IObserver> observers = new ArrayList<IObserver>();
		observers.add(this.obs);
		return observers;
	}

	@Override
	public IElement getModel() {
		return this.obs.rootNode;
	}
	

	@Override
	public UltimatePreferenceInitializer getPreferences() {
		return new PreferenceInitializer();
	}

}
