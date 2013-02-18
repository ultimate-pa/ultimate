package de.uni_freiburg.informatik.ultimate.plugins.output.jungvisualization.graph;

import java.util.HashMap;

import de.uni_freiburg.informatik.ultimate.model.structure.VisualizationEdge;
import de.uni_freiburg.informatik.ultimate.model.structure.VisualizationNode;
import de.uni_freiburg.informatik.ultimate.plugins.output.jungvisualization.editor.JungEditor;
import edu.uci.ics.jung.visualization.VisualizationViewer;

/**
 * Manages a HashMap with VisualizationViewers.
 * Designed according to the thread-safe singleton pattern.
 * 
 * @author lena
 *
 */

public class GraphHandler { //thread-safe singleton
	private static GraphHandler instance = new GraphHandler();
	
	private HashMap<Object,VisualizationViewer<VisualizationNode, VisualizationEdge>> visualizationViewers;
	private JungEditor lastCreatedEditor;
	private String lastCreatedVisualizationViewerID;
	final private static String MAX_VV_ID_SYSTEM_PROPERTY_KEY = "MaxVisViewerID";
	
	
	private GraphHandler(){
		this.visualizationViewers = new HashMap<Object,VisualizationViewer<VisualizationNode, VisualizationEdge>>();
	}
	
	/**
	 * Static method, returns the only instance of a singleton class.
	 * @return The only instance of GraphHandler.
	 */
	// static method, returns the only instance of a singleton class
	public static GraphHandler getInstance(){
		return instance;
	}
	
	/**
	 * Adds a given VisualizationViewer to a HashMap. 
	 * 
	 * @param vv {@link VisualizationViewer}
	 */	
	public void addVisualizationViewer(VisualizationViewer<VisualizationNode, VisualizationEdge> vv){

		String key = generateKey();
		this.visualizationViewers.put(key, vv);
		lastCreatedVisualizationViewerID = key;
	}
	
	/**
	 * Removes the {@link VisualizationViewer} for a specified key from the {@link HashMap}.
	 * @param key An object for accessing a {@link VisualizationViewer}.
	 */
	public void removeVisualizationViewer(String key){
		this.visualizationViewers.remove(key);
	}
	
	/**
	 * Generates a new key for a last created {@link VisualizationViewer} to store it in the {@link HashMap} 
	 * and stores this key in the system property "MaxVisViewerID" as ID of the {@link VisualizationViewer} attended
	 * to the last created {@link JungEditor}.
	 * 
	 * @return A new key for a last created VisualizationViewer to store it in the HashMap.
	 */
	private String generateKey(){
		String key = "0";
		if (System.getProperties().containsKey(MAX_VV_ID_SYSTEM_PROPERTY_KEY)){

			key = System.getProperty(MAX_VV_ID_SYSTEM_PROPERTY_KEY);
			int keyValue = Integer.parseInt(key) + 1;
			key = String.valueOf(keyValue);
		}
		System.setProperty(MAX_VV_ID_SYSTEM_PROPERTY_KEY, key);
		return key;
	}
	
	/**
	 * Returns ID of the VisualizationViewer attended to the last created JungEditor.
	 * @return ID of the VisualizationViewer attended to the last created JungEditor.
	 */
	public String getLastCreatedVisualizationViewerID(){
		
		return lastCreatedVisualizationViewerID;	
	}
	
	/**
	 * Returns a {@link VisualizationViewer} to the given key out of HashMap and null if
	 * the key is not in the HashMap.
	 * @param key An object for accessing a {@link VisualizationViewer}.
	 * @return A {@link VisualizationViewer} to the given key out of HashMap and null if
	 * the key is not in the HashMap.
	 */
	public VisualizationViewer<VisualizationNode, VisualizationEdge> getVisualizationViewer(Object key){
		
		if (this.visualizationViewers.containsKey(key)){
			
			return this.visualizationViewers.get(key);
		}
		else 
		{
			return null;
		}
	}
	
	/**
	 * Returns a {@link VisualizationViewer}.
	 * @return
	 */
	public VisualizationViewer<VisualizationNode, VisualizationEdge> getVisualizationViewer(){
		if (lastCreatedEditor != null){
			String key = lastCreatedEditor.getPartProperty(JungEditor.VV_ID_EDITOR_PROPERTY_KEY);
			return getVisualizationViewer(key);
		}
		else
		{
			return null;
		}
	}
	
	/**
	 * Returns a HashMap with VisualizationViewers of all opened in this session JV editors.
	 * 
	 * @return HashMap<Object,VisualizationViewer<VisualizationNode, String>>
	 */
	public HashMap<Object,VisualizationViewer<VisualizationNode, VisualizationEdge>> getVisualizationViewers(){
		return this.visualizationViewers;
	}

	/**
	 * Sets the last created JungEditor.
	 * @param je {@link JungEditor}
	 */
	public void setLastCreatedEditor(JungEditor je){
		this.lastCreatedEditor = je;
	}
	
}

